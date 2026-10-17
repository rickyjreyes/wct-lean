import importlib.util
import pathlib
import tempfile
import shutil
import unittest
ROOT=pathlib.Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('audit',ROOT/'scripts/audit_coverage.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
class Coverage(unittest.TestCase):
 def test_real_complement(self):
  d=audit.compute();self.assertEqual((d['typed'],d['registry_only']),(84,58))
  self.assertFalse(set(d['typed_ids'])&set(d['registry_only_ids']))
 def corrupted(self, relative, old, new):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);shutil.copytree(ROOT/'WCTLean',root/'WCTLean')
   p=root/relative;p.write_text(p.read_text().replace(old,new))
   with self.assertRaises(ValueError):audit.compute(root)
 def test_duplicate_id(self):
  self.corrupted('WCTLean/CoverageLedger.lean','"E15",','"E15", "E15",')
 def test_missing_declaration(self):
  self.corrupted('WCTLean/Models/ModalEntropyBounds.lean','theorem cumulative_dissipation_le_entropy_drop','theorem renamed')
 def test_wrong_lean_count(self):
  self.corrupted('WCTLean/CoverageLedger.lean','length = 84','length = 85')
if __name__=='__main__':unittest.main()
