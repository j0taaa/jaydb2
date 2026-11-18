use super::{Collection, Fields, StoreError, Value, value::name_valid};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColumnKind {
    TextValue,
    Boolean,
    Integer,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Column {
    pub name: String,
    pub kind: ColumnKind,
    pub optional: bool,
}

impl Column {
    fn fits(&self, value: &Value) -> bool {
        match value {
            Value::Absent => self.optional,
            Value::Text(_) => self.kind == ColumnKind::TextValue,
            Value::Bool(_) => self.kind == ColumnKind::Boolean,
            Value::Int(_) => self.kind == ColumnKind::Integer,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableSchema {
    pub name: String,
    pub key: String,
    pub columns: Vec<Column>,
}

impl TableSchema {
    pub(super) fn column_index(&self, name: &str) -> Option<usize> {
        self.columns
            .binary_search_by(|column| column.name.as_str().cmp(name))
            .ok()
    }

    fn valid(&self) -> bool {
        name_valid(&self.name)
            && self.columns.iter().all(|column| name_valid(&column.name))
            && self
                .columns
                .windows(2)
                .all(|pair| pair[0].name < pair[1].name)
            && self.column_index(&self.key).is_some_and(|index| {
                let column = &self.columns[index];
                column.kind == ColumnKind::TextValue && !column.optional
            })
    }

    pub(super) fn valid_row(&self, key: &str, fields: &Fields) -> bool {
        fields.len() == self.columns.len()
            && self
                .columns
                .iter()
                .zip(fields)
                .all(|(column, (name, value))| {
                    column.name == *name
                        && column.fits(value)
                        && (name != &self.key || matches!(value, Value::Text(text) if text == key))
                })
    }

    pub(super) fn valid_column_write(&self, index: usize, key: &str, value: &Value) -> bool {
        let column = &self.columns[index];
        column.fits(value)
            && (column.name != self.key || matches!(value, Value::Text(text) if text == key))
    }
}

#[derive(Debug)]
pub struct Schema {
    tables: Vec<TableSchema>,
    users: TableSchema,
    state_limit: u64,
}

impl Schema {
    /// Read a canonical value of the form
    /// `{tables: [{columns: [{kind: "TextValue", name: "id", optional: false}],
    /// key: "id", name: "example"}]}`. The other kind names are `"Boolean"`
    /// and `"Integer"`. The tables and columns follow Bend's strict name
    /// order. The fixed users schema is implicit. The state limit is in bytes.
    pub fn from_value(value: &Value, state_limit: u64) -> Result<Self, StoreError> {
        let Value::Record(root) = value else {
            return Err(StoreError::Data);
        };
        let [(name, Value::List(tables))] = root.as_slice() else {
            return Err(StoreError::Data);
        };
        if name != "tables" {
            return Err(StoreError::Data);
        }
        let mut schemas = Vec::new();
        for table in tables {
            let Value::Record(fields) = table else {
                return Err(StoreError::Data);
            };
            let [
                (cols, Value::List(columns)),
                (pk, Value::Text(key)),
                (label, Value::Text(name)),
            ] = fields.as_slice()
            else {
                return Err(StoreError::Data);
            };
            if cols != "columns" || pk != "key" || label != "name" {
                return Err(StoreError::Data);
            }
            let columns = columns
                .iter()
                .map(decode_column)
                .collect::<Result<_, _>>()?;
            schemas.push(TableSchema {
                name: name.clone(),
                key: key.clone(),
                columns,
            });
        }
        Self::new(schemas, state_limit)
    }

    pub fn new(tables: Vec<TableSchema>, state_limit: u64) -> Result<Self, StoreError> {
        if tables.iter().any(|table| !table.valid())
            || tables.windows(2).any(|pair| pair[0].name >= pair[1].name)
        {
            return Err(StoreError::Data);
        }
        let users = TableSchema {
            name: "users".to_owned(),
            key: "id".to_owned(),
            columns: ["credential", "id", "kind"]
                .map(|name| Column {
                    name: name.to_owned(),
                    kind: ColumnKind::TextValue,
                    optional: false,
                })
                .into(),
        };
        Ok(Self {
            tables,
            users,
            state_limit,
        })
    }

    pub fn tables(&self) -> &[TableSchema] {
        &self.tables
    }

    pub fn table(&self, collection: &Collection) -> Option<&TableSchema> {
        match collection {
            None => Some(&self.users),
            Some(name) => self
                .tables
                .binary_search_by(|table| table.name.cmp(name))
                .ok()
                .map(|index| &self.tables[index]),
        }
    }

    pub fn state_limit(&self) -> u64 {
        self.state_limit
    }
}

fn decode_column(value: &Value) -> Result<Column, StoreError> {
    let Value::Record(fields) = value else {
        return Err(StoreError::Data);
    };
    let [
        (ty, Value::Text(kind)),
        (label, Value::Text(name)),
        (opt, Value::Bool(optional)),
    ] = fields.as_slice()
    else {
        return Err(StoreError::Data);
    };
    if ty != "kind" || label != "name" || opt != "optional" {
        return Err(StoreError::Data);
    }
    let kind = match kind.as_str() {
        "TextValue" => ColumnKind::TextValue,
        "Boolean" => ColumnKind::Boolean,
        "Integer" => ColumnKind::Integer,
        _ => return Err(StoreError::Data),
    };
    Ok(Column {
        name: name.clone(),
        kind,
        optional: *optional,
    })
}
