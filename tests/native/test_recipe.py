"""First construction recipes. Success snapshots are separate fixtures only."""
import ctypes as C
import importlib.util
import mmap
from pathlib import Path
import tempfile
import unittest
from test_field import ROOT,U128,Wire,Result,Fixture,var,U64
SPEC=importlib.util.spec_from_file_location('recipe_build',ROOT/'tools/native/build_recipe.py')
BUILD=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(BUILD)
class Word(C.Structure):
    _fields_=[('payload',U64),('auxiliary',U64),('tag',U64)]
class Recipe(C.Structure):
    _fields_=[*[(n,U64) for n in ['operation','constructor_id','site_id','location','quantity']],
      ('wire',Wire),('scope',U128),('ceiling',U128),('deadline',U128),
      ('components',C.POINTER(Word)),('destinations',C.POINTER(C.POINTER(Word))),
      ('count',U64),('header',C.POINTER(Word)),('claim',C.POINTER(U64)),('claim_value',U64),
      ('completed_count',C.POINTER(U64)),('claim_count',C.POINTER(U64))]
class RecipeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb-recipes-');cls.directory=Path(cls.temp.name)
        cls.report=BUILD.build(cls.directory/'production.so')
        BUILD.build(cls.directory/'fixture.so',test_fixture=ROOT/'tests/native/recipe_fixture.c')
    @classmethod
    def tearDownClass(cls):cls.temp.cleanup()
    def invoke(self,*,operation=2,count=3,ceiling=100,flags=9,advance_at=0,advance_ns=0,
               wire_value=None,quantity=3,pending=0):
        lib=C.CDLL(str(self.directory/'fixture.so'))
        lib.jaydb_recipe_fixture.restype=C.POINTER(Fixture)
        f=lib.jaydb_recipe_fixture().contents;f.flags=flags;f.advance_at=advance_at;f.advance_ns=advance_ns
        lib.jaydb_field_recipe_stack_v3.restype=U64;extent=lib.jaydb_field_recipe_stack_v3()
        stack=mmap.mmap(-1,extent);stack[:]=bytes(extent);view=C.c_char.from_buffer(stack)
        self.addCleanup(stack.close);self.addCleanup(lambda:None)
        wire_value=var(4,3,b'abc') if wire_value is None else wire_value
        wire=C.create_string_buffer(wire_value)
        components=(Word*count)(*(Word(i+1,i+2,i+3) for i in range(count)))
        cells=(Word*count)(*(Word(0xa5,0xa5,0xa5) for _ in range(count)))
        pointers=(C.POINTER(Word)*count)(*(C.pointer(cells[i]) for i in range(count)))
        header=Word(0xa5,0xa5,0xa5);claim=U64(10)
        completed_count=U64();claim_count=U64()
        q=Recipe(operation,70000,90000,123,quantity,
          Wire(C.addressof(wire),len(wire_value),len(wire_value),0,0,U128.natural(pending)),
          U128.natural(7),U128.natural(ceiling),U128.natural(101),components,pointers,count,
          C.pointer(header),C.pointer(claim),999,C.pointer(completed_count),C.pointer(claim_count))
        r=Result();lib.jaydb_field_recipe_v3.argtypes=[C.POINTER(Recipe),C.c_void_p,U64,C.POINTER(Result)]
        lib.jaydb_field_recipe_v3(C.byref(q),C.addressof(view),extent,C.byref(r))
        del view
        self.last_totals=(completed_count.value,claim_count.value)
        return r,header,list(cells),claim.value,f
    def test_first_header_and_claim_are_built_under_equality_barrier(self):
        r,h,c,claim,f=self.invoke()
        self.assertEqual((r.status,r.constructed,claim,h.payload,h.auxiliary,h.tag),(0,1,999,123,70000,2))
        self.assertEqual((c[2].payload,c[2].auxiliary,c[2].tag),(3,4,5))
        self.assertEqual(f.releases,1)
        self.assertEqual(self.last_totals,(1,1))
    def test_immediate_and_scalar_have_no_prebuilt_header(self):
        for op,expected in [(0,(1,0,0)),(1,(1,70000,1))]:
            r,h,_,_,_=self.invoke(operation=op,count=1)
            self.assertEqual((r.status,h.payload,h.auxiliary,h.tag),(0,*expected))
    def test_primitive_fixed_extent_ignores_pending_but_variable_header_checks_it(self):
        for body,q in [(b'\0',0),(b'\1',0),(b'\2',0),(b'\3'+bytes(8),8)]:
            with self.subTest(body=body.hex()):
                r,h,_,claim,_=self.invoke(wire_value=body,quantity=q,pending=2**128-1)
                self.assertEqual((r.status,r.constructed,r.length_checked,claim),(0,1,1,999))
                self.assertEqual((r.quantity,r.position,r.tag),(q,0,body[0]))
        r,_,_,claim,f=self.invoke(pending=2**128-1)
        self.assertEqual((r.status,r.construction_started,r.stores_completed,claim,f.holds),(8,0,0,10,0))
    def test_incomplete_or_real_excess_cannot_claim_or_store(self):
        for options,expected in [({'flags':11},3),({'ceiling':99},1)]:
            r,h,c,claim,f=self.invoke(**options)
            self.assertEqual((r.status,r.stores_completed,claim),(expected,0,10))
            self.assertEqual((h.payload,h.auxiliary,h.tag),(0xa5,)*3)
            self.assertTrue(all(x.payload==0xa5 for x in c));self.assertEqual(f.releases,1)
    def test_no_arity_quota_and_timeout_retains_logical_claim_and_partial_stores(self):
        r,h,c,claim,f=self.invoke(count=513,advance_at=3,advance_ns=2)
        self.assertEqual((r.status,r.constructed,r.construction_started,r.stores_completed,claim),(2,0,1,128*24,999))
        self.assertEqual((c[127].payload,c[128].payload),(128,0xa5))
        self.assertEqual(h.payload,0xa5);self.assertEqual(f.releases,1)
        self.assertEqual(self.last_totals,(0,1))
        r,_,_,_,_=self.invoke(count=513);self.assertEqual(r.constructed,1)
    def test_expiry_after_last_store_preserves_real_completion(self):
        r,h,_,_,_=self.invoke(advance_at=4,advance_ns=2)
        self.assertEqual((r.status,r.constructed,h.tag),(2,1,2))
    def test_production_is_audited_leaf_without_test_symbols(self):
        self.assertTrue(self.report['criticalIsLeaf']);self.assertTrue(self.report['finalObjectHasNoCalls'])
        self.assertFalse(self.report['testFixture'])
if __name__=='__main__':unittest.main(verbosity=2)
