"""Lightweight correctness checks; these never compile or run JayDB2.

Run with: python3 -B -m unittest discover -s experiments/database-comparison -p test_suite.py -v
The complete ten-project catalog must exist before running the catalog tests.
"""
from __future__ import annotations

import copy
from pathlib import Path
import sqlite3
import tempfile
import unittest

import model
from sql_engines import SQL, quote

SUITE = Path(__file__).resolve().parent
SCENARIOS = SUITE / 'scenarios'
TABLE_COUNTS = [1, 3, 5, 8, 10, 12, 15, 18, 22, 26]


def load_named(prefix):
    paths = sorted(SCENARIOS.glob(prefix + '_*.json'))
    if len(paths) != 1:
        raise AssertionError(f'Expected one {prefix} scenario, found {paths}')
    return model.load(paths[0])


def populate(db, scenario):
    for table in scenario['tables']:
        for row in table['rows']:
            db.put(table['name'], row)


class ScenarioCatalogTests(unittest.TestCase):
    def test_ten_schemas_and_exact_complexity_levels(self):
        paths = sorted(SCENARIOS.glob('*.json'))
        self.assertEqual(len(paths), 10)
        for i, (path, count) in enumerate(zip(paths, TABLE_COUNTS, strict=True), 1):
            with self.subTest(project=path.stem):
                scenario = model.load(path)
                self.assertEqual(scenario['id'], path.stem)
                self.assertTrue(path.stem.startswith(f'{i:02}_'))
                self.assertEqual(len(scenario['tables']), count)
                self.assertTrue(all(len(t['rows']) == 8 for t in scenario['tables']))
                # Independently verify both dependency order and relationship values.
                parents = {}
                for table in scenario['tables']:
                    for column in table['columns']:
                        if 'references' in column:
                            parent, key = column['references'].split('.')
                            self.assertIn(parent, parents)
                            valid_keys = {r[key] for r in parents[parent]}
                            for row in table['rows']:
                                self.assertIn(row[column['name']], valid_keys)
                    parents[table['name']] = table['rows']

    def test_model_rejects_invalid_types_identity_and_relationships(self):
        good = load_named('04')
        inventory_index = next(i for i, t in enumerate(good['tables']) if t['name'] == 'inventory')
        cases = {}
        s = copy.deepcopy(good)
        s['tables'][inventory_index]['rows'][0]['quantity'] = True
        cases['bool_is_not_integer'] = s
        s = copy.deepcopy(good)
        s['tables'][inventory_index]['rows'][0]['quantity'] = 2**63
        cases['int64_overflow'] = s
        s = copy.deepcopy(good)
        s['tables'][inventory_index]['rows'][0]['product_id'] = 'nonexistent_product'
        cases['missing_parent'] = s
        s = copy.deepcopy(good)
        s['tables'][inventory_index]['columns'].append(copy.deepcopy(s['tables'][inventory_index]['columns'][0]))
        cases['duplicate_column'] = s
        s = copy.deepcopy(good)
        s['tables'][inventory_index]['rows'][1]['id'] = s['tables'][inventory_index]['rows'][0]['id']
        cases['duplicate_primary_key'] = s
        s = copy.deepcopy(good)
        inventory = s['tables'].pop(inventory_index)
        s['tables'].insert(0, inventory)
        cases['child_before_parent'] = s
        s = copy.deepcopy(good)
        del s['tables'][0]['rows'][0]['name']
        cases['incomplete_row'] = s
        for name, bad in cases.items():
            with self.subTest(case=name), self.assertRaises(AssertionError):
                model.validate(bad)

    def test_known_medium_project_aggregate_oracles(self):
        # Constants calculated from the business fixtures, independent of adapter code.
        for prefix, total in [('04', 257), ('05', 197000), ('06', 728)]:
            with self.subTest(project=prefix):
                scenario = load_named(prefix)
                a = scenario['aggregate']
                rows = model.state(scenario)[a['table']]
                self.assertEqual(sum(r[a['column']] for r in rows), total)

    def test_known_product_join_oracle(self):
        scenario = load_named('04')
        self.assertEqual(model.joined(scenario, model.state(scenario)), [
            ['line_1001_1', 'Cerrado beans 250g'],
            ['line_1002_1', 'Mogiana beans 1kg'],
            ['line_1003_1', 'Green tea 100g'],
            ['line_1004_1', 'Ceramic dripper'],
            ['line_1005_1', 'Stoneware mug'],
            ['line_1006_1', 'Almond biscuits'],
            ['line_1007_1', 'Paper filters 100 pack'],
            ['line_1008_1', 'Weekend tasting box'],
        ])

    def test_model_state_is_a_sorted_independent_copy(self):
        scenario = load_named('04')
        data = model.state(scenario)
        data['inventory'][0]['quantity'] = -123
        original = next(t for t in scenario['tables'] if t['name'] == 'inventory')
        self.assertTrue(all(r['quantity'] >= 0 for r in original['rows']))
        for table in data.values():
            self.assertEqual([r['id'] for r in table], sorted(r['id'] for r in table))


class SQLiteBehaviorTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='jaydb2-comparison-unit-')
        self.addCleanup(self.tmp.cleanup)
        self.scenario = load_named('04')
        self.db = SQL('sqlite', self.scenario, Path(self.tmp.name) / 'ecommerce', None)
        self.addCleanup(self.db.close)
        populate(self.db, self.scenario)

    def test_dump_and_business_queries(self):
        self.assertEqual(self.db.dump(), model.state(self.scenario))
        self.assertEqual(self.db.aggregate('inventory', 'quantity'), 257)
        self.assertEqual(self.db.join(self.scenario['join']), [
            ['line_1001_1', 'Cerrado beans 250g'],
            ['line_1002_1', 'Mogiana beans 1kg'],
            ['line_1003_1', 'Green tea 100g'],
            ['line_1004_1', 'Ceramic dripper'],
            ['line_1005_1', 'Stoneware mug'],
            ['line_1006_1', 'Almond biscuits'],
            ['line_1007_1', 'Paper filters 100 pack'],
            ['line_1008_1', 'Weekend tasting box'],
        ])
        self.assertIs(self.db.get('products', 'prod_cerrado', 'active'), True)

    def test_foreign_key_and_strict_type_failures_preserve_row(self):
        before = self.db.dump()
        with self.assertRaises(sqlite3.IntegrityError):
            self.db.update('inventory', 'stock_gift_cwb', 'product_id', 'missing_product')
        with self.assertRaises(sqlite3.IntegrityError):
            self.db.update('inventory', 'stock_gift_cwb', 'quantity', 'wrong-type')
        with self.assertRaises(sqlite3.IntegrityError):
            self.db.update('products', 'prod_cerrado', 'active', 2)
        duplicate = copy.deepcopy(self.scenario['tables'][0]['rows'][0])
        with self.assertRaises(sqlite3.IntegrityError):
            self.db.put('customers', duplicate)
        self.assertEqual(self.db.dump(), before)

    def test_failed_second_write_rolls_back_first(self):
        before = self.db.dump()
        with self.assertRaises(sqlite3.IntegrityError):
            self.db.batch([
                ('inventory', 'stock_cerrado_sp', 'quantity', 111),
                ('inventory', 'stock_gift_cwb', 'quantity', 'wrong-type'),
            ])
        self.assertEqual(self.db.dump(), before)
        self.db.batch([
            ('inventory', 'stock_cerrado_sp', 'quantity', 43),
            ('inventory', 'stock_gift_cwb', 'quantity', 10),
        ])
        self.assertEqual(self.db.get('inventory', 'stock_cerrado_sp', 'quantity'), 43)
        self.assertEqual(self.db.get('inventory', 'stock_gift_cwb', 'quantity'), 10)

    def test_committed_changes_survive_reopen(self):
        self.db.update('inventory', 'stock_gift_cwb', 'quantity', 19)
        before = self.db.dump()
        self.assertGreater(self.db.size_bytes(), 0)
        self.db.reopen()
        self.assertEqual(self.db.dump(), before)
        self.assertEqual(self.db.get('inventory', 'stock_gift_cwb', 'quantity'), 19)
        self.assertEqual(self.db.conn.execute('PRAGMA foreign_keys').fetchone()[0], 1)
        self.assertEqual(self.db.conn.execute('PRAGMA synchronous').fetchone()[0], 2)

    def test_bound_text_values_do_not_change_sql_structure(self):
        value = "O'Neil; DROP TABLE customers; -- café ☕"
        self.db.update('customers', 'cust_ana', 'name', value)
        self.assertEqual(self.db.get('customers', 'cust_ana', 'name'), value)
        self.assertEqual(len(self.db.keys('customers')), 8)
        self.assertIsNone(self.db.get('customers', 'missing_customer', 'name'))

    def test_all_ten_sqlite_schemas_round_trip(self):
        paths = sorted(SCENARIOS.glob('*.json'))
        self.assertEqual(len(paths), 10)
        for path in paths:
            with self.subTest(project=path.stem):
                scenario = model.load(path)
                db = SQL('sqlite', scenario, Path(self.tmp.name) / path.stem, None)
                try:
                    populate(db, scenario)
                    self.assertEqual(db.dump(), model.state(scenario))
                    a = scenario['aggregate']
                    self.assertEqual(db.aggregate(a['table'], a['column']),
                                     sum(r[a['column']] for r in model.state(scenario)[a['table']]))
                    if scenario['join']:
                        self.assertEqual(db.join(scenario['join']), model.joined(scenario, model.state(scenario)))
                    db.reopen()
                    self.assertEqual(db.dump(), model.state(scenario))
                finally:
                    db.close()


class SQLIdentifierTests(unittest.TestCase):
    def test_reserved_words_are_quoted_and_unsafe_names_rejected(self):
        self.assertEqual(quote('primary'), '"primary"')
        self.assertEqual(quote('order'), '"order"')
        for value in ['orders; DROP TABLE orders', 'a.b', 'x"y', '', 'one two', '1table', None]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                quote(value)


if __name__ == '__main__':
    unittest.main()
