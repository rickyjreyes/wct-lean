"""Regression checks for the conservative source-token screen."""
import unittest
from audit_formal_sources import FORBIDDEN, source_tokens

class SourceAuditTests(unittest.TestCase):
    def test_inline_placeholders(self):
        for text in ("theorem t : True := by sorry", "by admit",
                     "private axiom fake : False", "by native_decide",
                     "set_option debug.skipKernelTC true"):
            with self.subTest(text=text):
                self.assertTrue(set(source_tokens(text)) & FORBIDDEN)

    def test_comments_and_strings(self):
        text = '/- outer /- sorry -/ axiom -/\n-- admit\ndef s := "native_decide"'
        self.assertFalse(set(source_tokens(text)) & FORBIDDEN)

    def test_nested_comment_followed_by_bypass(self):
        self.assertIn("sorry", set(source_tokens("/- /- text -/ -/ by sorry")))

    def test_unterminated_comment_fails(self):
        with self.assertRaises(ValueError):
            list(source_tokens("/- unclosed"))

if __name__ == "__main__":
    unittest.main()
