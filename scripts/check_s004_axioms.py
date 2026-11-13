#!/usr/bin/env python3
"""Fail closed on unexpected axioms in the 96 maintained corrected S004 proofs."""
from pathlib import Path
import re
import sys

EXPECTED_ROOTS = 96
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("Usage: check_s004_axioms.py s004-axioms.log")

text = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, flags=re.S)
axiom_free = re.findall(r"does not depend on any axioms", text)
total = len(blocks) + len(axiom_free)
if total != EXPECTED_ROOTS:
    raise SystemExit(
        f"Expected {EXPECTED_ROOTS} theorem axiom reports, found {total}; refusing a partial audit"
    )
unexpected = sorted({
    item.strip()
    for block in blocks
    for item in block.split(",")
    if item.strip() and item.strip() not in ALLOWED
})
if unexpected:
    raise SystemExit(f"Nonstandard axioms detected in S004 proof chain: {unexpected}")
print(
    f"PASS: {total} S004 declarations audited; "
    f"only {sorted(ALLOWED)} permitted; no unexpected axioms"
)
