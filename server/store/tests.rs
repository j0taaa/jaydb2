use super::*;
use value::{decode_envelope, encode_envelope};

fn text(value: &str) -> Value {
    Value::Text(value.to_owned())
}

fn record(fields: impl IntoIterator<Item = (&'static str, Value)>) -> Value {
    Value::Record(
        fields
            .into_iter()
            .map(|(name, value)| (name.to_owned(), value))
            .collect(),
    )
}

fn table() -> Collection {
    Some("items".to_owned())
}

fn schema(limit: u64) -> Schema {
    let columns = [
        ("flag", ColumnKind::Boolean, true),
        ("id", ColumnKind::TextValue, false),
        ("number", ColumnKind::Integer, false),
        ("text", ColumnKind::TextValue, true),
    ];
    Schema::new(
        vec![TableSchema {
            name: table().unwrap(),
            key: "id".to_owned(),
            columns: columns
                .into_iter()
                .map(|(name, kind, optional)| Column {
                    name: name.to_owned(),
                    kind,
                    optional,
                })
                .collect(),
        }],
        limit,
    )
    .unwrap()
}

fn fields(key: &str, number: i64, value: Value) -> Fields {
    record([
        ("flag", Value::Absent),
        ("id", text(key)),
        ("number", Value::Int(number)),
        ("text", value),
    ])
    .into_fields()
    .unwrap()
}

fn item(key: &str, number: i64) -> Operation {
    Operation::DefineRow {
        collection: table(),
        key: key.to_owned(),
        fields: fields(key, number, Value::Absent),
    }
}

fn user(key: &str, credential: &str, kind: &str) -> Operation {
    Operation::DefineRow {
        collection: None,
        key: key.to_owned(),
        fields: record([
            ("credential", text(credential)),
            ("id", text(key)),
            ("kind", text(kind)),
        ])
        .into_fields()
        .unwrap(),
    }
}

fn change(collection: Collection, key: &str, column: &str, value: Value) -> Operation {
    Operation::DefineColumn {
        collection,
        key: key.to_owned(),
        column: column.to_owned(),
        value,
    }
}

fn read(collection: Collection, key: &str, column: &str) -> Operation {
    Operation::ReadCell {
        collection,
        key: key.to_owned(),
        column: column.to_owned(),
    }
}

fn remove(collection: Collection, key: &str) -> Operation {
    Operation::RemoveRow {
        collection,
        key: key.to_owned(),
    }
}

fn state(limit: u64) -> Snapshot {
    let snapshot = Snapshot::empty(schema(limit), 0).unwrap();
    let mut tx = snapshot.begin();
    assert_eq!(tx.operate(item("a", 10)), Answer::Changed);
    assert_eq!(
        tx.operate(user("alice", "secret", "admin")),
        Answer::Changed
    );
    tx.commit(&snapshot, 1).unwrap()
}

#[test]
fn store_codec() {
    let value = record([
        (
            "_ascii7",
            Value::List(vec![
                Value::Absent,
                Value::Bool(false),
                Value::Bool(true),
                Value::Int(i64::MIN),
                Value::Int(i64::MAX),
                text("É\0🌳"),
            ]),
        ),
        ("empty", record([])),
        ("list", Value::List(vec![])),
    ]);
    let bytes = encode(&value).unwrap();
    assert_eq!(decode(&bytes), Ok(value));
    assert_eq!(
        encode(&Value::Int(-1)).unwrap(),
        [3, 255, 255, 255, 255, 255, 255, 255, 255]
    );
    assert_eq!(
        encode(&text("é")).unwrap(),
        [4, 0, 0, 0, 0, 0, 0, 0, 2, 0xc3, 0xa9]
    );
    for end in 0..bytes.len() {
        assert_eq!(decode(&bytes[..end]), Err(CodecError));
    }
    for invalid in [
        vec![0, 0],
        vec![7],
        vec![5, 255, 255, 255, 255, 255, 255, 255, 255],
        vec![4, 0, 0, 0, 0, 0, 0, 0, 3, 0xed, 0xa0, 0x80], // surrogate
        vec![4, 0, 0, 0, 0, 0, 0, 0, 2, 0xc0, 0x80],       // overlong NUL
    ] {
        assert_eq!(decode(&invalid), Err(CodecError));
    }
    for invalid in [
        record([("z", Value::Absent), ("a", Value::Absent)]),
        record([("a", Value::Absent), ("a", Value::Absent)]),
        record([("é", Value::Absent)]),
        record([("0a", Value::Absent)]),
    ] {
        assert_eq!(encode(&invalid), Err(CodecError));
        assert_eq!(
            decode(&encode_envelope(&invalid.into_fields().unwrap())),
            Err(CodecError)
        );
    }

    let mut deep = Vec::new();
    for _ in 0..20_000 {
        write_list_header(&mut deep, 1);
    }
    deep.push(0);
    assert_eq!(encode(&decode(&deep).unwrap()).unwrap(), deep);
}

#[test]
fn store_schema_and_root() {
    let parsed = Schema::from_value(
        &record([(
            "tables",
            Value::List(vec![record([
                (
                    "columns",
                    Value::List(vec![record([
                        ("kind", text("TextValue")),
                        ("name", text("id")),
                        ("optional", Value::Bool(false)),
                    ])]),
                ),
                ("key", text("id")),
                ("name", text("users")),
            ])]),
        )]),
        10_000,
    )
    .unwrap();
    assert_eq!(parsed.tables()[0].name, "users");
    assert_eq!(parsed.table(&None).unwrap().columns.len(), 3);
    assert_eq!(
        parsed
            .table(&Some("users".to_owned()))
            .unwrap()
            .columns
            .len(),
        1
    );

    let snapshot = state(10_000);
    let bytes = encode(&record([
        (
            "tables",
            Value::List(vec![record([
                ("name", text("items")),
                (
                    "rows",
                    Value::List(vec![Value::Record(fields("a", 10, Value::Absent))]),
                ),
            ])]),
        ),
        (
            "users",
            Value::List(vec![record([
                ("credential", text("secret")),
                ("id", text("alice")),
                ("kind", text("admin")),
            ])]),
        ),
    ]))
    .unwrap();
    assert_eq!(snapshot.save(), bytes);
    assert_eq!(
        Snapshot::load(schema(10_000), 17, &bytes).unwrap().lsn(),
        17
    );
    assert_eq!(
        Snapshot::load(schema(10_000), 17, &bytes).unwrap().save(),
        bytes
    );

    let wrong_row_order = record([
        (
            "tables",
            Value::List(vec![record([
                ("name", text("items")),
                (
                    "rows",
                    Value::List(vec![
                        Value::Record(fields("z", 1, Value::Absent)),
                        Value::Record(fields("a", 2, Value::Absent)),
                    ]),
                ),
            ])]),
        ),
        ("users", Value::List(vec![])),
    ]);
    assert_eq!(
        Snapshot::load(schema(0), 0, &encode(&wrong_row_order).unwrap()).err(),
        Some(StoreError::Data)
    );
    assert_eq!(
        Snapshot::load(schema(0), 0, &bytes).err(),
        Some(StoreError::Limit)
    );
}

#[test]
fn store_operations() {
    let base = state(10_000);
    let mut tx = base.begin();
    let absent = || Operation::Existence {
        collection: table(),
        key: "missing".to_owned(),
    };
    let missing = Some("unknown".to_owned());
    assert_eq!(
        tx.operate(read(table(), "missing", "text")),
        Answer::RowAbsent
    );
    assert_eq!(
        tx.operate(read(table(), "a", "text")),
        Answer::Cell(Value::Absent)
    );
    assert_eq!(
        tx.operate(read(table(), "missing", "bad")),
        Answer::FailureData
    );
    assert_eq!(tx.operate(absent()), Answer::Existence(false));
    assert_eq!(
        tx.operate(Operation::Existence {
            collection: table(),
            key: "a".to_owned()
        }),
        Answer::Existence(true)
    );
    assert_eq!(
        tx.operate(Operation::Existence {
            collection: missing.clone(),
            key: "a".to_owned()
        }),
        Answer::FailureData
    );
    assert_eq!(
        tx.operate(Operation::Count {
            collection: table()
        }),
        Answer::Count(1)
    );
    assert_eq!(
        tx.operate(Operation::Count {
            collection: missing.clone()
        }),
        Answer::FailureData
    );
    assert_eq!(
        tx.operate(Operation::Keys {
            collection: missing.clone()
        }),
        Answer::FailureData
    );
    for key in ["é", "🙂", "", "a\0", "Z", "aa"] {
        assert_eq!(tx.operate(item(key, 20)), Answer::Changed);
    }
    assert_eq!(
        tx.operate(Operation::Keys {
            collection: table()
        }),
        Answer::Keys(
            ["", "Z", "a", "a\0", "aa", "é", "🙂"]
                .map(str::to_owned)
                .into(),
        )
    );
    assert_eq!(tx.operate(item("a", 42)), Answer::Changed);
    assert_eq!(
        tx.operate(read(table(), "a", "number")),
        Answer::Cell(Value::Int(42))
    );
    for fields in [
        fields("wrong", 1, Value::Absent),
        fields("a", 1, Value::Bool(true)),
        fields("a", 1, Value::Absent).into_iter().rev().collect(),
        fields("a", 1, Value::Absent).into_iter().skip(1).collect(),
    ] {
        assert_eq!(
            tx.operate(Operation::DefineRow {
                collection: table(),
                key: "a".into(),
                fields
            }),
            Answer::FailureData
        );
    }
    assert_eq!(
        tx.operate(change(table(), "a", "id", text("a"))),
        Answer::Changed
    );
    assert_eq!(
        tx.operate(change(table(), "a", "text", text("new"))),
        Answer::Changed
    );
    assert_eq!(
        tx.operate(read(table(), "a", "text")),
        Answer::Cell(text("new"))
    );
    assert_eq!(
        tx.operate(change(table(), "missing", "flag", Value::Bool(true))),
        Answer::Changed
    );
    assert_eq!(tx.operate(absent()), Answer::Existence(false));
    assert_eq!(
        tx.operate(change(table(), "missing", "id", text("wrong"))),
        Answer::FailureData
    );
    assert_eq!(
        tx.operate(change(table(), "a", "number", Value::Absent)),
        Answer::FailureData
    );
    assert_eq!(
        tx.operate(change(table(), "a", "bad", Value::Absent)),
        Answer::FailureData
    );
    assert_eq!(tx.operate(remove(table(), "a")), Answer::Changed);
    assert_eq!(tx.operate(remove(table(), "a")), Answer::Changed);
    assert_eq!(tx.operate(read(table(), "a", "id")), Answer::RowAbsent);
    assert_eq!(tx.operate(remove(missing, "a")), Answer::FailureData);

    let mut old = base.begin();
    assert_eq!(
        old.operate(read(table(), "a", "number")),
        Answer::Cell(Value::Int(10))
    );
    assert_eq!(
        old.operate(Operation::Count {
            collection: table()
        }),
        Answer::Count(1)
    );
}

#[test]
fn store_occ_rows_and_membership() {
    let base = state(10_000);
    let mut observe = base.begin();
    observe.operate(read(table(), "a", "id"));
    let mut count = base.begin();
    count.operate(Operation::Count {
        collection: table(),
    });
    let mut insert = base.begin();
    insert.operate(item("b", 2));
    let mut update = base.begin();
    update.operate(item("a", 3));
    let mut no_op = base.begin();
    no_op.operate(change(table(), "b", "text", text("other")));

    let current = update.commit(&base, 2).unwrap();
    assert_eq!(observe.validate(&current), Err(StoreError::Conflict));
    assert_eq!(count.validate(&current), Ok(()));
    assert_eq!(no_op.validate(&current), Ok(()));

    let current = insert.commit(&current, 3).unwrap();
    assert_eq!(count.validate(&current), Err(StoreError::Conflict));
    assert_eq!(no_op.validate(&current), Err(StoreError::Conflict));

    let mut remove_b = current.begin();
    remove_b.operate(remove(table(), "b"));
    let current = remove_b.commit(&current, 4).unwrap();
    assert_eq!(no_op.validate(&current), Err(StoreError::Conflict)); // tombstone
    assert_eq!(count.validate(&current), Err(StoreError::Conflict)); // add then remove

    let mut writer = base.begin();
    writer.operate(item("a", 10));
    assert_eq!(writer.commit(&current, 5).err(), Some(StoreError::Conflict));
    assert_eq!(
        current.begin().commit(&current, 4).err(),
        Some(StoreError::InvalidLsn)
    );
}

#[test]
fn store_prunes_only_versions_no_running_snapshot_needs() {
    let base = state(10_000);
    let mut row_reader = base.begin();
    row_reader.operate(read(table(), "a", "id"));
    let mut auth_reader = base.begin();
    assert_eq!(auth_reader.authenticate("rotated"), None);

    let mut change = base.begin();
    change.operate(remove(table(), "a"));
    change.operate(user("alice", "rotated", "admin"));
    let mut current = change.commit(&base, 2).unwrap();

    current.prune_versions(base.lsn());
    assert_eq!(row_reader.validate(&current), Err(StoreError::Conflict));
    assert_eq!(auth_reader.validate(&current), Err(StoreError::Conflict));

    let fresh = current.begin();
    let canonical = current.save();
    current.prune_versions(current.lsn());
    assert!(
        current
            .collections
            .iter()
            .all(|(_, table)| table.last_write.is_empty())
    );
    assert!(current.credential_lsn.is_empty());
    assert_eq!(fresh.validate(&current), Ok(()));
    assert_eq!(current.save(), canonical);
    assert_eq!(current.authenticate("rotated").unwrap().id, "alice");
}

#[test]
fn store_credentials_and_final_order() {
    let base = state(10_000);
    let mut seen = base.begin();
    let mut missed = base.begin();
    assert_eq!(seen.authenticate("secret").unwrap().kind, "admin");
    assert_eq!(missed.authenticate("rotated"), None);

    let mut added = base.begin();
    added.operate(user("bob", "secret", "member"));
    assert_eq!(added.authenticate("secret").unwrap().id, "alice");
    assert_eq!(added.commit(&base, 2).err(), Some(StoreError::Data));

    let mut redeclare = base.begin();
    redeclare.operate(user("alice", "secret", "reader"));
    let current = redeclare.commit(&base, 2).unwrap();
    assert_eq!(seen.validate(&current), Err(StoreError::Conflict));
    assert_eq!(missed.validate(&current), Ok(()));

    let mut swap = current.begin();
    swap.operate(user("bob", "secret", "member"));
    swap.operate(user("alice", "rotated", "reader"));
    assert_eq!(swap.authenticate("secret").unwrap().id, "bob");
    let writes = swap.write_set();
    let next = swap.commit(&current, 3).unwrap();
    assert_eq!(next.authenticate("rotated").unwrap().id, "alice");
    assert_eq!(next.authenticate("secret").unwrap().id, "bob");
    assert_eq!(
        current.apply_write_set(3, &writes).unwrap().save(),
        next.save()
    );
    assert_eq!(missed.validate(&next), Err(StoreError::Conflict));

    let limit = base.canonical_size();
    let small = Snapshot::load(schema(limit), 1, &base.save()).unwrap();
    let mut invalid = small.begin();
    invalid.operate(user("bob", "", "member"));
    assert_eq!(invalid.commit(&small, 2).err(), Some(StoreError::Data));
    let mut valid = small.begin();
    valid.operate(user("bob", "unique", "member"));
    assert_eq!(valid.commit(&small, 2).err(), Some(StoreError::Limit));
    assert_eq!(small.authenticate("secret").unwrap().id, "alice");
}

#[test]
fn store_size_after_random_writes_and_replay() {
    let mut current = state(100_000);
    let mut random = 130_801_259u32;
    for lsn in 2..130 {
        let mut tx = current.begin();
        for i in 0..7 {
            random = random.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let key = (random % 37).to_string();
            let operation = match (random >> 16) % 5 {
                0 => remove(table(), &key),
                1 => change(table(), &key, "text", text(&"å🪶".repeat(i))),
                2 => user(&key, &format!("cred-{key}-{i}"), "kind"),
                3 => remove(None, &key),
                _ => item(&key, i64::from(random)),
            };
            assert_eq!(tx.operate(operation), Answer::Changed);
        }
        let writes = tx.write_set();
        let staged = tx.commit(&current, lsn).unwrap();
        let bytes = staged.save();
        assert_eq!(staged.canonical_size(), bytes.len() as u64);
        assert_eq!(encode(&decode(&bytes).unwrap()).unwrap(), bytes);
        assert_eq!(current.apply_write_set(lsn, &writes).unwrap().save(), bytes);
        assert_eq!(
            Snapshot::load(schema(100_000), lsn, &bytes).unwrap().save(),
            bytes
        );
        current = staged;
    }
    assert_eq!(
        current
            .apply_write_set(200, &[(table(), "a".into(), Some(vec![0]))])
            .err(),
        Some(StoreError::Data)
    );
    assert_eq!(
        current
            .apply_write_set(200, &[(None, "a".into(), None), (None, "a".into(), None)])
            .err(),
        Some(StoreError::Data)
    );
}

#[test]
fn store_abi() {
    let mut tx = state(10_000).begin();
    let value = record([
        ("op", text("read_cell")),
        ("collection", text("items")),
        ("key", text("a")),
        ("column", text("number")),
    ]);
    let bytes = encode_envelope(&value.into_fields().unwrap());
    assert_eq!(decode(&bytes), Err(CodecError));
    let op = Operation::decode(&bytes).unwrap();
    assert_eq!(op, read(table(), "a", "number"));
    assert_eq!(
        tx.operate(op).encode(),
        encode(&record([
            ("result", text("cell")),
            ("value", Value::Int(10)),
        ]))
        .unwrap()
    );
    let authenticating = record([("op", text("authenticate")), ("credential", text("secret"))]);
    let auth = Operation::decode(&encode_envelope(&authenticating.into_fields().unwrap())).unwrap();
    let user = decode_envelope(&tx.operate(auth).encode()).unwrap();
    assert_eq!(
        user,
        record([
            ("result", text("user")),
            ("id", text("alice")),
            ("kind", text("admin")),
            ("credential", text("secret")),
        ])
        .into_fields()
        .unwrap()
    );

    let wrong = record([("collection", Value::Absent), ("op", text("count"))]);
    assert_eq!(Operation::decode(&encode(&wrong).unwrap()), Err(CodecError));
    let extra = record([
        ("op", text("count")),
        ("collection", Value::Absent),
        ("extra", Value::Absent),
    ]);
    assert_eq!(Operation::from_value(extra), Err(CodecError));
}

#[test]
#[ignore = "run python3 tools/live/store_reference.py to generate the Bend oracle fixtures"]
fn store_reference() {
    fn from_hex(hex: &str) -> Vec<u8> {
        let (octets, remainder) = hex.as_bytes().as_chunks::<2>();
        assert!(remainder.is_empty(), "incomplete fixture octet");
        octets
            .iter()
            .map(|octet| u8::from_str_radix(std::str::from_utf8(octet).unwrap(), 16).unwrap())
            .collect()
    }
    let fixture =
        std::fs::read_to_string(std::env::var_os("STORE_REFERENCE_CASES").unwrap()).unwrap();
    for (case, line) in fixture.lines().enumerate() {
        let parts: Vec<_> = line.split_ascii_whitespace().map(from_hex).collect();
        let [root, operation, expected] = parts.as_slice() else {
            panic!("fixture shape")
        };
        let snapshot = Snapshot::load(schema(100_000), 0, root).unwrap();
        assert_eq!(snapshot.save(), *root, "initial state in case {case}");
        let mut tx = snapshot.begin();
        let op = Operation::decode(operation).unwrap();
        let desc = format!("{op:?}");
        let mut answer = tx.operate(op).into_value().into_fields().unwrap();
        answer.sort_by(|(left, _), (right, _)| left.cmp(right));
        let rows = |collection: &Collection| {
            Value::List(
                tx.rows(collection)
                    .values()
                    .map(|row| row.value.clone())
                    .collect(),
            )
        };
        let working = record([
            (
                "tables",
                Value::List(vec![record([
                    ("name", text("items")),
                    ("rows", rows(&table())),
                ])]),
            ),
            ("users", rows(&None)),
        ]);
        let actual = record([("answer", Value::Record(answer)), ("state", working)]);
        assert_eq!(
            encode(&actual).unwrap(),
            *expected,
            "case {case}, {desc}; expected {:?}, got {actual:?}",
            decode(expected).unwrap()
        );
    }
    assert!(fixture.lines().count() >= 300);
}
