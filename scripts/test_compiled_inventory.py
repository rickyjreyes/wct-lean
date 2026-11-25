"""Exercise the production Lean audit against three compiled miniature roots."""
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

TEMPLATE = Path(__file__).with_name("strict_axiom_audit.template").read_text()


def main():
    toolchain = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    lean = str(Path(toolchain) / "bin/lean")
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "WCTLean").mkdir()
        env = dict(os.environ, LEAN_PATH=str(root))

        def compile_module(name, source):
            path = root / (name + ".lean")
            path.write_text(source)
            subprocess.run([lean, "-o", name + ".olean", name + ".lean"],
                           cwd=root, env=env, check=True)

        compile_module("WCTLean/Target", "import Lean\n")
        audit = TEMPLATE.replace("@MODULES@", "`WCTLean.Registry, `WCTLean.Main")
        audit = audit.replace("@IMPORTS@", "`WCTLean.Target")
        audit = audit.replace("@THEOREMS@", "`WCTLean.required")
        (root / "Audit.lean").write_text(
            "import WCTLean.Main\nimport WCTLean.Target\nimport WCTLean.Registry\n" + audit)
        for root_import, declaration, error in [
            ("import WCTLean.Target", "theorem", None),
            ("-- import WCTLean.Target", "theorem", "missing direct import"),
            ("import WCTLean.Target", "def", "expected a registry theorem"),
        ]:
            compile_module("WCTLean/Main", "import Lean\n" + root_import + "\n")
            compile_module("WCTLean/Registry",
                           f"import Lean\n-- theorem required\n{declaration} WCTLean.required : True := True.intro\n")
            result = subprocess.run([lean, "Audit.lean"], cwd=root, env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if (result.returncode == 0) != (error is None) or (error and error not in result.stdout):
                raise RuntimeError(result.stdout)
            print(error or "valid registry accepted")


if __name__ == "__main__":
    main()
