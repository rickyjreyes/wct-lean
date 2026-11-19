#!/usr/bin/env python3
"""Fail closed on unexpected axioms in a `#print axioms` log.

Usage: check_axiom_log.py LOG EXPECTED_ROOTS LABEL

Requires exactly EXPECTED_ROOTS axiom reports (refusing partial audits) and
permits only Lean's standard foundational axioms.
"""
from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 4:
    raise SystemExit("Usage: check_axiom_log.py LOG EXPECTED_ROOTS LABEL")

log, expected, label = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
text = log.read_text(encoding="utf-8", errors="replace")
if re.search(r"(?m)^.*\berror\b", text):
    raise SystemExit(f"{label}: Lean reported an error while printing axioms")
blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, flags=re.S)
axiom_free = re.findall(r"does not depend on any axioms", text)
total = len(blocks) + len(axiom_free)
if total != expected:
    raise SystemExit(
        f"{label}: expected {expected} theorem axiom reports, found {total}; "
        "refusing a partial audit"
    )
unexpected = sorted({
    item.strip()
    for block in blocks
    for item in block.split(",")
    if item.strip() and item.strip() not in ALLOWED
})
if unexpected:
    raise SystemExit(f"{label}: nonstandard axioms detected: {unexpected}")
print(f"PASS: {total} {label} declarations audited; only {sorted(ALLOWED)} permitted")
