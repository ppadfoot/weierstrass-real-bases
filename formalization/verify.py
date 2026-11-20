"""Recompile the project's Lean sources against the locked, prebuilt mathlib.

Uses standard Lean module setup files to read public mathlib interfaces. No
project object files from previous runs are on the import path.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
PACKAGES = ROOT / ".lake" / "packages"
IMPORT = re.compile(r"^(?:public )?import (Weierstrass(?:\.\w+)*)$", re.MULTILINE)


def dependency_interfaces():
    roots = [pkg / ".lake/build/lib/lean" for pkg in sorted(PACKAGES.iterdir())]
    interfaces = {}
    for lib in roots:
        for path in lib.rglob("*.olean"):
            name = ".".join(path.relative_to(lib).with_suffix("").parts)
            if name in interfaces:
                raise ValueError(f"Two dependencies define {name}")
            ir = path.with_suffix(".ir")
            signature = path.with_suffix(".ir.sig")
            parts = [str(path)]
            server, private = Path(str(path) + ".server"), Path(str(path) + ".private")
            if server.is_file() and private.is_file():
                parts.extend([str(server), str(private)])
            interfaces[name] = [parts, [str(signature), str(ir)] if signature.is_file() and ir.is_file() else []]
    return roots, interfaces


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true",
                        help="also require an unconditional proof of Theorem 1.1")
    args = parser.parse_args()
    pin = (ROOT / "lean-toolchain").read_text().strip().split(":v")[-1]
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    if f"version {pin}," not in version:
        raise SystemExit(f"Expected Lean {pin}, found {version}")
    print(version, flush=True)
    if not PACKAGES.is_dir():
        raise SystemExit("Install the locked dependencies and their mathlib cache first. See README.")
    roots, interfaces = dependency_interfaces()
    if "Mathlib.Topology.MetricSpace.HausdorffDimension" not in interfaces:
        raise SystemExit("Missing mathlib Hausdorff-dimension module. See README.")
    sources = {f"Weierstrass.{p.stem}": p for p in (ROOT / "Weierstrass").glob("*.lean")}
    sources.update(Weierstrass=ROOT / "Weierstrass.lean", Audit=ROOT / "Audit.lean")
    with tempfile.TemporaryDirectory(prefix="weierstrass-proof-") as temp:
        out = Path(temp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [out, *roots])))
        done = set()

        def check(name):
            if name in done:
                return
            path = sources[name]
            for dep in IMPORT.findall(path.read_text()):
                check(dep)
            setup = out / "setup.json"
            setup.write_text(json.dumps(dict(name=name, isModule=True, importArts=interfaces,
                                              options={}, plugins=[], dynlibs=[])))
            target = out.joinpath(*name.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {name}", flush=True)
            subprocess.run(["lean", "-DwarningAsError=true", f"--setup={setup}", "-o",
                            str(target), str(path)], env=env, cwd=ROOT, check=True)
            done.add(name)

        check("Audit")
        detached = sorted(set(sources) - done)
        if detached:
            raise SystemExit("Missing from the public entry point: " + ", ".join(detached))
        if args.full:
            # The audit has already checked transitive axioms of all public project theorems.
            # Type-checking this term also rejects an implication with missing hypotheses.
            target = out / "CheckMain.lean"
            target.write_text("module\nimport Weierstrass\n"
                              "example : Weierstrass.MainStatement := Weierstrass.main_theorem\n"
                              "#print axioms Weierstrass.main_theorem\n")
            setup = out / "setup-full.json"
            setup.write_text(json.dumps(dict(name="CheckMain", isModule=True,
                                              importArts=interfaces, options={}, plugins=[], dynlibs=[])))
            print("Checking the unconditional all-real-base theorem", flush=True)
            result = subprocess.run(["lean", "-DwarningAsError=true", f"--setup={setup}", str(target)],
                                    env=env, cwd=ROOT)
            if result.returncode:
                raise SystemExit("Full verification failed. The unconditional proof of MainStatement did not type-check.")



if __name__ == "__main__":
    main()
