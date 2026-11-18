use super::{
    CodecError, Fields, Value,
    value::{decode_envelope, encode_envelope},
};

/// The user registry is None. Application tables are Some(table_name).
pub type Collection = Option<String>;

#[derive(Debug, PartialEq, Eq)]
pub enum Operation {
    Authenticate {
        credential: String,
    },
    ReadCell {
        collection: Collection,
        key: String,
        column: String,
    },
    Existence {
        collection: Collection,
        key: String,
    },
    Count {
        collection: Collection,
    },
    Keys {
        collection: Collection,
    },
    DefineRow {
        collection: Collection,
        key: String,
        fields: Fields,
    },
    DefineColumn {
        collection: Collection,
        key: String,
        column: String,
        value: Value,
    },
    RemoveRow {
        collection: Collection,
        key: String,
    },
}

impl Operation {
    /// Decode the body after the worker's 0x02 operation discriminator.
    pub fn decode(bytes: &[u8]) -> Result<Self, CodecError> {
        Self::from_value(Value::Record(decode_envelope(bytes)?))
    }

    /// Interpret the exact outer field order specified by the worker ABI.
    pub fn from_value(value: Value) -> Result<Self, CodecError> {
        let mut fields = value.into_fields()?.into_iter();
        let mut field = |expected: &str| match fields.next() {
            Some((name, value)) if name == expected => Ok(value),
            _ => Err(CodecError),
        };
        let op = field("op")?.into_text()?;
        let operation = if op == "authenticate" {
            Self::Authenticate {
                credential: field("credential")?.into_text()?,
            }
        } else {
            let collection = match field("collection")? {
                Value::Absent => None,
                name => Some(name.into_text()?),
            };
            match op.as_str() {
                "read_cell" => Self::ReadCell {
                    collection,
                    key: field("key")?.into_text()?,
                    column: field("column")?.into_text()?,
                },
                "existence" => Self::Existence {
                    collection,
                    key: field("key")?.into_text()?,
                },
                "count" => Self::Count { collection },
                "keys" => Self::Keys { collection },
                "define_row" => Self::DefineRow {
                    collection,
                    key: field("key")?.into_text()?,
                    fields: field("fields")?.into_fields()?,
                },
                "define_column" => Self::DefineColumn {
                    collection,
                    key: field("key")?.into_text()?,
                    column: field("column")?.into_text()?,
                    value: field("value")?,
                },
                "remove_row" => Self::RemoveRow {
                    collection,
                    key: field("key")?.into_text()?,
                },
                _ => return Err(CodecError),
            }
        };
        fields
            .next()
            .is_none()
            .then_some(operation)
            .ok_or(CodecError)
    }

    pub(super) fn collection(&self) -> &Collection {
        match self {
            Self::ReadCell { collection, .. }
            | Self::Existence { collection, .. }
            | Self::Count { collection }
            | Self::Keys { collection }
            | Self::DefineRow { collection, .. }
            | Self::DefineColumn { collection, .. }
            | Self::RemoveRow { collection, .. } => collection,
            Self::Authenticate { .. } => unreachable!("authentication has its own path"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct User {
    pub id: String,
    pub kind: String,
    pub credential: String,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Answer {
    RowAbsent,
    Cell(Value),
    Existence(bool),
    Count(usize),
    Keys(Vec<String>),
    Changed,
    FailureData,
    User(User),
    NoUser,
}

impl Answer {
    /// Build the ordered ABI envelope.
    pub fn into_value(self) -> Value {
        let (result, payload) = match self {
            Self::RowAbsent => ("row_absent", vec![]),
            Self::Cell(value) => ("cell", vec![("value", value)]),
            Self::Existence(exists) => ("existence", vec![("exists", Value::Bool(exists))]),
            Self::Count(count) => {
                let count =
                    i64::try_from(count).expect("row count is bounded by its canonical state size");
                ("count", vec![("count", Value::Int(count))])
            }
            Self::Keys(keys) => (
                "keys",
                vec![(
                    "keys",
                    Value::List(keys.into_iter().map(Value::Text).collect()),
                )],
            ),
            Self::Changed => ("changed", vec![]),
            Self::FailureData => ("data_error", vec![]),
            Self::User(user) => (
                "user",
                vec![
                    ("id", Value::Text(user.id)),
                    ("kind", Value::Text(user.kind)),
                    ("credential", Value::Text(user.credential)),
                ],
            ),
            Self::NoUser => ("no_user", vec![]),
        };
        let mut fields = vec![("result".to_owned(), Value::Text(result.to_owned()))];
        fields.extend(
            payload
                .into_iter()
                .map(|(name, value)| (name.to_owned(), value)),
        );
        Value::Record(fields)
    }

    /// Encode the ABI answer body in the documented field order.
    pub fn encode(self) -> Vec<u8> {
        let fields = self
            .into_value()
            .into_fields()
            .expect("answers are records");
        encode_envelope(&fields)
    }
}
