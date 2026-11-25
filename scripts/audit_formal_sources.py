#!/usr/bin/env python3
"""Audit Lean source closure and emit deterministic SHA-256 metadata."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = {"sorry", "admit", "axiom", "sorryAx", "native_decide", "ofReduceBool", "unsafe", "implemented_by", "skipKernelTC", "trustCompiler", "extern", "partial", "opaque", "csimp"}
TOKEN = re.compile(r"[\w'!?]+")

REQUIRED_IMPORTS = (
    "WCTLean.Models.D4Binding",
    "WCTLean.Models.D4Analytical",
    "WCTLean.Models.D4Closure",
    "WCTLean.Registry",
    "WCTLean.Dimension",
    "WCTLean.Curvature",
    "WCTLean.Energy",
    "WCTLean.Koide",
    "WCTLean.Fourier",
    "WCTLean.Contracts.Analytic",
    "WCTLean.Models.CurvatureOperator",
    "WCTLean.Models.ComplexCurvature",
    "WCTLean.Models.PhaseFlux",
    "WCTLean.Models.RestDensity",
    "WCTLean.Models.Locking",
    "WCTLean.Models.BandPass",
    "WCTLean.Models.AlgebraicChecks",
    "WCTLean.Models.LogFlow",
    "WCTLean.Models.GhostModes",
    "WCTLean.Models.Collider",
    "WCTLean.Models.KoideDerivation",
    "WCTLean.Models.UnifiedOperator",
    "WCTLean.Models.CompactDynamics",
    "WCTLean.ResolvedAudit",
    "WCTLean.DerivedAudit",
)
REQUIRED_STATEMENTS = """\
example : WCTLean.allEquationIds.length = 142 := WCTLean.allEquationIds_length
example : WCTLean.allEquationIds.Nodup := WCTLean.allEquationIds_nodup
example : WCTLean.statusPartition.toFinset = WCTLean.allEquationIds.toFinset := WCTLean.statusPartition_complete
example : WCTLean.canonicalRegistry.length = 142 := WCTLean.canonicalRegistry_length
"""

REQUIRED_THEOREMS = (
    "allEquationIds_length",
    "allEquationIds_nodup",
    "statusPartition_complete",
    "canonicalRegistry_length",
)


def visible_code(text: str) -> str:
    """Conservative lexical screen; nested comments and ordinary strings are ignored.
    The elaborated dependency audit is authoritative, not this screen.
    """
    result = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(text):
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for pos in range(start, i):
            if result[pos] != "\n":
                result[pos] = " "
    return "".join(result)


def source_tokens(text: str):
    return TOKEN.findall(visible_code(text))


def generate_strict_audit(paths: list[Path], output: Path) -> None:
    modules = [p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".") for p in paths]
    if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", m) for m in modules):
        raise SystemExit("Unrecognized module path in strict audit inventory")
    template = (ROOT / "scripts" / "strict_axiom_audit.template").read_text(encoding="utf-8")
    output.write_text(
        "\n".join("import " + m for m in modules) + "\n\n" +
        (template.replace("@MODULES@", ", ".join("`" + m for m in modules))
         .replace("@IMPORTS@", ", ".join("`" + m for m in REQUIRED_IMPORTS))
         .replace("@THEOREMS@", ", ".join("`WCTLean." + n for n in REQUIRED_THEOREMS))
         .replace("@STATEMENTS@", REQUIRED_STATEMENTS)),
        encoding="utf-8",
    )


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def inventory(root: Path, container: bool) -> set[Path]:
    manifest = json.loads((root / "scripts/lean-source-paths.json").read_text())
    if container:
        actual = []
        for directory, children, names in os.walk(root):
            if Path(directory) == root:
                children[:] = [name for name in children if name not in {".lake", ".git"}]
            actual.extend((Path(directory) / name).relative_to(root).as_posix()
                          for name in names if name.endswith(".lean"))
    else:
        raw = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"], cwd=root)
        actual = [os.fsdecode(path) for path in raw.split(b"\0") if path]
    if manifest != sorted(actual):
        missing = sorted(set(manifest) - set(actual))
        extra = sorted(set(actual) - set(manifest))
        raise SystemExit(f"Lean source inventory mismatch: missing={missing}, extra={extra}")
    for name in actual:
        path = root / name
        if not path.is_file() or path.resolve() != path:
            raise SystemExit(f"Missing or symlinked Lean source: {name}")
    return {root / name for name in actual}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "formal-source-hashes.json")
    parser.add_argument("--strict-lean-output", type=Path)
    parser.add_argument("--container-inventory", action="store_true")
    args = parser.parse_args()

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    expected_version = toolchain.rsplit(":v", 1)[-1]
    if f'@ "v{expected_version}"' not in lakefile:
        raise SystemExit("lean-toolchain and mathlib version in lakefile.lean differ")

    legacy_files = {ROOT / "Main.lean", ROOT / "MyProject.lean", *(ROOT / "MyProject").rglob("*.lean")}
    source_files = sorted([ROOT / "WCTLean.lean", *(ROOT / "WCTLean").rglob("*.lean"), *legacy_files])
    failures: list[str] = []
    files: dict[str, str] = {}
    for path in source_files:
        text = path.read_text(encoding="utf-8")
        forbidden = sorted(set(source_tokens(text)) & FORBIDDEN)
        if forbidden:
            failures.append(f"forbidden source tokens {forbidden} in {path.relative_to(ROOT)}")
        files[path.relative_to(ROOT).as_posix()] = sha256(path)

    # Inventory every tracked Lean path; non-library tooling is separately hashed.
    tracked_paths = inventory(ROOT, args.container_inventory)
    tooling = {ROOT / p for p in (
        "lakefile.lean",
        "scripts/analytic_integrity_axioms.lean",
        "scripts/complex_closure_nonuniqueness_axiom_audit.lean",
        "scripts/complex_curvature_limit_axiom_audit.lean",
        "scripts/d4_axiom_audit.lean",
        "scripts/s004_axiom_audit.lean",
    )}
    unclassified = tracked_paths - set(source_files) - tooling
    for path in sorted(unclassified):
        failures.append(f"unclassified Lean file: {path.relative_to(ROOT)}")
    tooling_hashes = {p.relative_to(ROOT).as_posix(): sha256(p) for p in sorted(tooling)}

    root_text = (ROOT / "WCTLean" / "Main.lean").read_text(encoding="utf-8")
    root_code = visible_code(root_text)
    for required in REQUIRED_IMPORTS:
        if not re.search(r"(?m)^\s*import[ \t]+" + re.escape(required) + r"[ \t]*$", root_code):
            failures.append(f"WCTLean/Main.lean does not import {required}")

    registry_text = (ROOT / "WCTLean" / "Registry.lean").read_text(encoding="utf-8")
    registry_code = visible_code(registry_text)
    for required_theorem in REQUIRED_THEOREMS:
        if not re.search(r"(?m)^\s*theorem[ \t]+" + re.escape(required_theorem) + r"(?=[\s:])", registry_code):
            failures.append(f"WCTLean/Registry.lean lacks {required_theorem}")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next((row for row in manifest.get("packages", []) if row.get("name") == "mathlib"), None)
    if not mathlib:
        failures.append("lake-manifest.json has no mathlib package")

    if args.strict_lean_output and not failures:
        generate_strict_audit(source_files, args.strict_lean_output)

    output = {
        "schema_version": "2.0.0",
        "lean_toolchain": toolchain,
        "mathlib_input_revision": mathlib.get("inputRev") if mathlib else None,
        "mathlib_commit": mathlib.get("rev") if mathlib else None,
        "source_file_count": len(files),
        "source_sha256": files,
        "tracked_lean_file_count": len(tracked_paths),
        "tooling_sha256": tooling_hashes,
        "lake_manifest_sha256": sha256(ROOT / "lake-manifest.json"),
        "lakefile_sha256": sha256(ROOT / "lakefile.lean"),
        "status": "PASS" if not failures else "FAIL",
        "failures": failures,
    }
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2, sort_keys=True))
    if failures:
        raise SystemExit("Formal-source audit failed:\n- " + "\n- ".join(failures))


if __name__ == "__main__":
    main()
