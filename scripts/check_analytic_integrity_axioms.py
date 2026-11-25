"""Require complete focused axiom reports and reject nonstandard axioms."""
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text(encoding="utf-8")
allowed = {"propext", "Classical.choice", "Quot.sound"}
blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, flags=re.S)
free = re.findall(r"does not depend on any axioms", text)
if len(blocks) + len(free) != 10:
    raise SystemExit("Incomplete focused integrity audit")
unexpected = {x.strip() for b in blocks for x in b.split(",") if x.strip()} - allowed
if unexpected:
    raise SystemExit(f"Unexpected axioms: {sorted(unexpected)}")
print("PASS: all 10 focused integrity declarations use only allowed axioms")
