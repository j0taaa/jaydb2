use std::{error::Error, fmt, mem};

pub type Fields = Vec<(String, Value)>;

/// A Bend value with a proper list or record spine and Unicode scalar text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Absent,
    Bool(bool),
    Int(i64),
    Text(String),
    List(Vec<Value>),
    Record(Fields),
}

// Canonical values have no depth limit. Dispose of nested values iteratively
// as well, including when a malformed input leaves a partial decoded value.
impl Drop for Value {
    fn drop(&mut self) {
        fn needs_drain(value: &Value) -> bool {
            matches!(value, Value::List(items) if !items.is_empty())
                || matches!(value, Value::Record(fields) if !fields.is_empty())
        }

        fn drain(value: &mut Value, pending: &mut Vec<Value>) {
            match value {
                Value::List(items) => pending.extend(items.drain(..).filter(needs_drain)),
                Value::Record(fields) => {
                    pending.extend(fields.drain(..).map(|(_, v)| v).filter(needs_drain));
                }
                _ => {}
            }
        }

        if needs_drain(self) {
            let mut pending = Vec::new();
            drain(self, &mut pending);
            while let Some(mut value) = pending.pop() {
                drain(&mut value, &mut pending);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodecError;

impl fmt::Display for CodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid value encoding")
    }
}

impl Error for CodecError {}

pub(super) fn name_valid(name: &str) -> bool {
    let mut bytes = name.bytes();
    name.len() <= 64
        && bytes
            .next()
            .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

pub(super) const HEADER: usize = 9;

pub(super) fn text_size(text: &str) -> usize {
    HEADER + text.len()
}

fn header(out: &mut Vec<u8>, tag: u8, len: usize) {
    out.push(tag);
    out.extend_from_slice(&(len as u64).to_be_bytes());
}

pub(super) fn write_text(out: &mut Vec<u8>, text: &str) {
    header(out, 4, text.len());
    out.extend_from_slice(text.as_bytes());
}

pub(super) fn write_list_header(out: &mut Vec<u8>, len: usize) {
    header(out, 5, len);
}

pub(super) fn write_record_header(out: &mut Vec<u8>, len: usize) {
    header(out, 6, len);
}

enum Item<'a> {
    Value(&'a Value),
    Name(&'a str),
}

fn write_fields<'a>(out: &mut Vec<u8>, pending: &mut Vec<Item<'a>>, fields: &'a Fields) {
    write_record_header(out, fields.len());
    for (name, value) in fields.iter().rev() {
        pending.push(Item::Value(value));
        pending.push(Item::Name(name));
    }
}

fn write_items(out: &mut Vec<u8>, mut pending: Vec<Item<'_>>) -> Result<(), CodecError> {
    while let Some(item) = pending.pop() {
        match item {
            Item::Value(Value::Absent) => out.push(0),
            Item::Value(Value::Bool(value)) => out.push(if *value { 2 } else { 1 }),
            Item::Value(Value::Int(value)) => {
                out.push(3);
                out.extend_from_slice(&value.to_be_bytes());
            }
            Item::Value(Value::Text(text)) => write_text(out, text),
            Item::Value(Value::List(items)) => {
                write_list_header(out, items.len());
                pending.extend(items.iter().rev().map(Item::Value));
            }
            Item::Value(Value::Record(fields)) => {
                if fields.iter().any(|(name, _)| !name_valid(name))
                    || fields.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                {
                    return Err(CodecError);
                }
                write_fields(out, &mut pending, fields);
            }
            Item::Name(name) => write_text(out, name),
        }
    }
    Ok(())
}

/// Encode one value using contract/Protocol.bend.
pub fn encode(value: &Value) -> Result<Vec<u8>, CodecError> {
    let mut out = Vec::new();
    write_value(&mut out, value)?;
    Ok(out)
}

pub(super) fn write_value(out: &mut Vec<u8>, value: &Value) -> Result<(), CodecError> {
    write_items(out, vec![Item::Value(value)])
}

// The worker ABI prescribes field order on its outer record. Values inside
// that record still use the canonical codec.
pub(super) fn encode_envelope(fields: &Fields) -> Vec<u8> {
    let mut out = Vec::new();
    let mut pending = Vec::new();
    write_fields(&mut out, &mut pending, fields);
    write_items(&mut out, pending).expect("answer values are canonical");
    out
}

struct Decoder<'a>(&'a [u8]);

impl<'a> Decoder<'a> {
    fn take(&mut self, len: usize) -> Result<&'a [u8], CodecError> {
        let (head, tail) = self.0.split_at_checked(len).ok_or(CodecError)?;
        self.0 = tail;
        Ok(head)
    }

    fn word(&mut self) -> Result<[u8; 8], CodecError> {
        Ok(self.take(8)?.try_into().unwrap())
    }

    fn len(&mut self) -> Result<usize, CodecError> {
        usize::try_from(u64::from_be_bytes(self.word()?)).map_err(|_| CodecError)
    }

    fn text(&mut self) -> Result<String, CodecError> {
        let len = self.len()?;
        let text = std::str::from_utf8(self.take(len)?).map_err(|_| CodecError)?;
        Ok(text.to_owned())
    }

    fn name(&mut self) -> Result<String, CodecError> {
        if self.take(1)? != [4] {
            return Err(CodecError);
        }
        let name = self.text()?;
        name_valid(&name).then_some(name).ok_or(CodecError)
    }

    fn value(&mut self) -> Result<Value, CodecError> {
        let mut stack = Vec::<Frame>::new();
        'values: loop {
            let mut value = match self.take(1)?[0] {
                0 => Value::Absent,
                1 => Value::Bool(false),
                2 => Value::Bool(true),
                3 => Value::Int(i64::from_be_bytes(self.word()?)),
                4 => Value::Text(self.text()?),
                tag @ (5 | 6) => {
                    let remaining = self.len()?;
                    let contents = if tag == 5 {
                        Value::List(Vec::new())
                    } else {
                        Value::Record(Vec::new())
                    };
                    if remaining != 0 {
                        // A record entry needs a text header, a name byte and a value tag.
                        let min_size = if tag == 5 { 1 } else { HEADER + 2 };
                        if remaining > self.0.len() / min_size {
                            return Err(CodecError);
                        }
                        let name = if tag == 6 { Some(self.name()?) } else { None };
                        stack.push(Frame {
                            remaining,
                            contents,
                            name,
                        });
                        continue;
                    }
                    contents
                }
                _ => return Err(CodecError),
            };

            while let Some(frame) = stack.last_mut() {
                match &mut frame.contents {
                    Value::List(items) => items.push(value),
                    Value::Record(fields) => fields.push((frame.name.take().unwrap(), value)),
                    _ => unreachable!(),
                }
                frame.remaining -= 1;
                if frame.remaining == 0 {
                    value = stack.pop().unwrap().contents;
                    continue;
                }
                if let Value::Record(fields) = &frame.contents {
                    let name = self.name()?;
                    if fields.last().unwrap().0 >= name {
                        return Err(CodecError);
                    }
                    frame.name = Some(name);
                }
                continue 'values;
            }
            return Ok(value);
        }
    }
}

struct Frame {
    remaining: usize,
    contents: Value,
    name: Option<String>,
}

/// Decode exactly one canonical value, consuming all input bytes.
pub fn decode(bytes: &[u8]) -> Result<Value, CodecError> {
    let mut decoder = Decoder(bytes);
    let value = decoder.value()?;
    decoder.0.is_empty().then_some(value).ok_or(CodecError)
}

pub(super) fn decode_envelope(bytes: &[u8]) -> Result<Fields, CodecError> {
    let mut decoder = Decoder(bytes);
    if decoder.take(1)? != [6] {
        return Err(CodecError);
    }
    let len = decoder.len()?;
    let mut fields = Vec::new();
    for _ in 0..len {
        fields.push((decoder.name()?, decoder.value()?));
    }
    decoder.0.is_empty().then_some(fields).ok_or(CodecError)
}

impl Value {
    pub(super) fn into_fields(mut self) -> Result<Fields, CodecError> {
        match &mut self {
            Self::Record(fields) => Ok(mem::take(fields)),
            _ => Err(CodecError),
        }
    }

    pub(super) fn into_list(mut self) -> Result<Vec<Value>, CodecError> {
        match &mut self {
            Self::List(items) => Ok(mem::take(items)),
            _ => Err(CodecError),
        }
    }

    pub(super) fn into_text(mut self) -> Result<String, CodecError> {
        match &mut self {
            Self::Text(text) => Ok(mem::take(text)),
            _ => Err(CodecError),
        }
    }
}
