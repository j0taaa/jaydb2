//! Bounded advisory routing only. Every doubt returns None to checked dispatch.
//! No status, principal, registry entry or publication decision originates here.

struct Cursor<'a> {
    rest: &'a [u8],
}

impl<'a> Cursor<'a> {
    fn take(&mut self, count: usize) -> Option<&'a [u8]> {
        let (value, rest) = self.rest.split_at_checked(count)?;
        self.rest = rest;
        Some(value)
    }

    fn byte(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }

    fn count(&mut self) -> Option<usize> {
        usize::try_from(u64::from_be_bytes(self.take(8)?.try_into().ok()?)).ok()
    }

    fn text(&mut self) -> Option<&'a str> {
        if self.byte()? != 4 {
            return None;
        }
        let size = self.count()?;
        std::str::from_utf8(self.take(size)?).ok()
    }

    fn field(&mut self, expected: &str) -> Option<()> {
        (self.text()? == expected).then_some(())
    }

    // At most 64 recursive containers; each iteration consumes an input byte.
    // Larger valid values simply take the ordinary checked dispatch path.
    fn value(&mut self, depth: usize) -> Option<()> {
        if depth > 64 {
            return None;
        }
        match *self.rest.first()? {
            0..=2 => {
                self.take(1)?;
            }
            3 => {
                self.take(9)?;
            }
            4 => {
                self.text()?;
            }
            5 | 6 => {
                let record = self.byte()? == 6;
                let count = self.count()?;
                if count > self.rest.len() {
                    return None;
                }
                let mut previous: Option<&str> = None;
                for _ in 0..count {
                    if record {
                        let name = self.text()?;
                        let mut bytes = name.bytes();
                        if name.len() > 64
                            || !bytes
                                .next()
                                .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
                            || !bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
                            || previous.is_some_and(|p| p >= name)
                        {
                            return None;
                        }
                        previous = Some(name);
                    }
                    self.value(depth + 1)?;
                }
            }
            _ => return None,
        }
        Some(())
    }
}

pub fn candidate(body: &[u8], message_limit: u64) -> Option<&str> {
    if body.len() as u64 > message_limit {
        return None;
    }
    let mut cursor = Cursor { rest: body };
    if cursor.take(3)? != [7, 1, 6] || cursor.count()? != 4 {
        return None;
    }
    cursor.field("arguments")?;
    cursor.value(0)?;
    cursor.field("code")?;
    let handle = cursor.text()?;
    if handle.len() != 64
        || !handle
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return None;
    }
    cursor.field("credential")?;
    cursor.text()?;
    cursor.field("proof")?;
    cursor.text()?;
    cursor.rest.is_empty().then_some(handle)
}

/// Checked envelope: tag 6, framed environment, optional route/principal, match/ready flags,
/// then unchanged Commit/Keep. Parse metadata before considering publication.
pub struct Checked<'a> {
    pub environment: &'a str,
    pub route: Option<&'a str>,
    pub principal: Option<&'a str>,
    pub artifact_matches: bool,
    pub authentication_ready: bool,
    pub decision: &'a [u8],
}

impl Checked<'_> {
    pub fn accepts_candidate(&self, candidate: &str, environment: &str) -> bool {
        self.environment == environment
            && self.route == Some(candidate)
            && self.artifact_matches
            && self.authentication_ready
    }
}

fn optional_text<'a>(cursor: &mut Cursor<'a>) -> Option<Option<&'a str>> {
    match cursor.byte()? {
        0 => Some(None),
        1 => {
            let size = cursor.count()?;
            Some(Some(std::str::from_utf8(cursor.take(size)?).ok()?))
        }
        _ => None,
    }
}

pub fn checked(output: &[u8]) -> Option<Checked<'_>> {
    let mut cursor = Cursor { rest: output };
    if cursor.byte()? != 6 {
        return None;
    }
    let environment_size = cursor.count()?;
    let environment = std::str::from_utf8(cursor.take(environment_size)?).ok()?;
    let route = optional_text(&mut cursor)?;
    let principal = optional_text(&mut cursor)?;
    let artifact_matches = match cursor.byte()? {
        0 => false,
        1 => true,
        _ => return None,
    };
    let authentication_ready = match cursor.byte()? {
        0 => false,
        1 => true,
        _ => return None,
    };
    Some(Checked {
        environment,
        route,
        principal,
        artifact_matches,
        authentication_ready,
        decision: cursor.rest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn text(value: &str, out: &mut Vec<u8>) {
        out.push(4);
        out.extend_from_slice(&(value.len() as u64).to_be_bytes());
        out.extend_from_slice(value.as_bytes());
    }
    fn request(arguments: &[u8]) -> Vec<u8> {
        let mut out = vec![7, 1, 6];
        out.extend_from_slice(&4u64.to_be_bytes());
        text("arguments", &mut out);
        out.extend_from_slice(arguments);
        for (key, value) in [
            ("code", "a".repeat(64)),
            ("credential", "token".into()),
            ("proof", "".into()),
        ] {
            text(key, &mut out);
            text(&value, &mut out);
        }
        out
    }
    #[test]
    fn candidate_is_total_and_conservative() {
        let body = request(&[0]);
        assert_eq!(candidate(&body, u64::MAX), Some("a".repeat(64).as_str()));
        for end in 0..body.len() {
            assert!(candidate(&body[..end], u64::MAX).is_none());
        }
        assert!(candidate(&body, body.len() as u64 - 1).is_none());
        for op in [0, 2, 3, 255] {
            let mut other = body.clone();
            other[1] = op;
            assert!(candidate(&other, u64::MAX).is_none());
        }
        let mut extra = body.clone();
        extra.push(0);
        assert!(candidate(&extra, u64::MAX).is_none());
        assert!(
            candidate(
                &request(&[5, 255, 255, 255, 255, 255, 255, 255, 255]),
                u64::MAX
            )
            .is_none()
        );
        let mut deep = Vec::new();
        for _ in 0..66 {
            deep.push(5);
            deep.extend_from_slice(&1u64.to_be_bytes());
        }
        deep.push(0);
        assert!(candidate(&request(&deep), u64::MAX).is_none());
        // All one-byte mutations and their truncations must remain total.
        for index in 0..body.len() {
            for byte in 0..=255 {
                let mut altered = body.clone();
                altered[index] = byte;
                candidate(&altered, u64::MAX);
            }
        }
    }
    #[test]
    fn metadata_distinguishes_empty_principal_and_rejects_truncations() {
        let mut bytes = vec![6];
        bytes.extend_from_slice(&1u64.to_be_bytes());
        bytes.push(b'e');
        bytes.push(1);
        bytes.extend_from_slice(&1u64.to_be_bytes());
        bytes.push(b'h');
        bytes.push(1);
        bytes.extend_from_slice(&0u64.to_be_bytes());
        bytes.extend_from_slice(&[0, 1, 0, 9]);
        let parsed = checked(&bytes).unwrap();
        assert_eq!(parsed.route, Some("h"));
        assert_eq!(parsed.principal, Some(""));
        assert!(!parsed.artifact_matches);
        assert!(!parsed.accepts_candidate("h", "e"));
        assert_eq!(parsed.decision, &[0, 9]);
        for end in 0..bytes.len() - 2 {
            assert!(checked(&bytes[..end]).is_none());
        }
        let flag = bytes.len() - 4;
        bytes[flag] = 1;
        let parsed = checked(&bytes).unwrap();
        assert!(parsed.accepts_candidate("h", "e"));
        assert!(!parsed.accepts_candidate("h", "wrong-environment"));
        assert!(!parsed.accepts_candidate("wrong-handle", "e"));
        bytes[flag + 1] = 0;
        assert!(!checked(&bytes).unwrap().accepts_candidate("h", "e"));
    }
}
