"""Regression tests for the configured Palomar module-source layout.

Tests run in a disposable source-only copy; real dependencies and caches are
never modified. Synthetic dependency roots represent the manifest packages.
"""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix="palomar-layout-test-") as tmp:
        trial = Path(tmp)
        shutil.copytree(
            ROOT, trial, dirs_exist_ok=True,
            ignore=shutil.ignore_patterns(".lake", ".git", "__pycache__"),
        )
        manifest = json.loads((trial / "lake-manifest.json").read_text())
        packages = trial / manifest.get("packagesDir", ".lake/packages")
        for package in manifest["packages"]:
            (packages / package["name"]).mkdir(parents=True)
        dependency = packages / "large_indecomposable"
        for old_name in ["Challenge", "Solution"]:
            (dependency / (old_name + ".lean")).write_text("module\n")
        config = json.loads((trial / "comparator.json").read_text())
        top_names = sorted({config[key].split(".")[0]
                            for key in ["challenge_module", "solution_module"]})

        def check(accept, label, diagnostic=None):
            result = subprocess.run(
                [sys.executable, str(trial / "scripts/check_integrity.py")],
                capture_output=True, text=True, check=False,
            )
            if (result.returncode == 0) != accept:
                raise AssertionError((label, result.stdout, result.stderr))
            if diagnostic and diagnostic not in result.stderr:
                raise AssertionError((label, result.stderr))
            print("PASS:", label)

        check(True, "new layout accepts dependency root Challenge/Solution")
        for top in top_names:
            collision = dependency / top
            collision.mkdir()
            check(False, "dependency directory collision rejected: " + top,
                  "is shadowed by dependency large_indecomposable")
            collision.rmdir()
            collision = dependency / (top + ".lean")
            collision.write_text("module\n")
            check(False, "dependency Lean-file collision rejected: " + top,
                  "is shadowed by dependency large_indecomposable")
            collision.unlink()
        empty_dependency = packages / "mathlib"
        empty_dependency.rmdir()
        check(False, "unavailable dependency cannot silently pass audit",
              "Dependency unavailable for module collision audit: mathlib")
        empty_dependency.mkdir()
        check(True, "restored source-only layout accepted")


if __name__ == "__main__":
    main()
