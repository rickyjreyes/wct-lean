#!/usr/bin/env python3
"""Audit Lean source closure and emit deterministic SHA-256 metadata."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"(?m)^\s*(sorry|admit)\b")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "formal-source-hashes.json")
    args = parser.parse_args()

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    expected_version = toolchain.rsplit(":v", 1)[-1]
    if f'@ "v{expected_version}"' not in lakefile:
        raise SystemExit("lean-toolchain and mathlib version in lakefile.lean differ")

    source_files = sorted([ROOT / "WCTLean.lean", *(ROOT / "WCTLean").rglob("*.lean")])
    failures: list[str] = []
    files: dict[str, str] = {}
    for path in source_files:
        text = path.read_text(encoding="utf-8")
        if FORBIDDEN.search(text):
            failures.append(f"placeholder proof token in {path.relative_to(ROOT)}")
        files[path.relative_to(ROOT).as_posix()] = sha256(path)

    root_text = (ROOT / "WCTLean" / "Main.lean").read_text(encoding="utf-8")
    for required in (
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
    ):
        if f"import {required}" not in root_text:
            failures.append(f"WCTLean/Main.lean does not import {required}")

    registry_text = (ROOT / "WCTLean" / "Registry.lean").read_text(encoding="utf-8")
    for required_theorem in (
        "allEquationIds_length",
        "allEquationIds_nodup",
        "statusPartition_complete",
        "canonicalRegistry_length",
    ):
        if f"theorem {required_theorem}" not in registry_text:
            failures.append(f"WCTLean/Registry.lean lacks {required_theorem}")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next((row for row in manifest.get("packages", []) if row.get("name") == "mathlib"), None)
    if not mathlib:
        failures.append("lake-manifest.json has no mathlib package")

    output = {
        "schema_version": "2.0.0",
        "lean_toolchain": toolchain,
        "mathlib_input_revision": mathlib.get("inputRev") if mathlib else None,
        "mathlib_commit": mathlib.get("rev") if mathlib else None,
        "source_file_count": len(files),
        "source_sha256": files,
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
