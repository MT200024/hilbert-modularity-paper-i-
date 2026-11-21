#!/usr/bin/env python3
"""Check project-local imports and count the explicit proof admissions."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
project = root / "HilbertModularity"
files = sorted([*root.glob("*.lean"), *project.rglob("*.lean")])
pattern = re.compile(r"^\s*(?:public )?import\s+(HilbertModularity(?:\.[A-Za-z_0-9]+)+)\s*$", re.M)
missing = []
admissions = []
introduced = []
imports = 0

for file in files:
    relative = file.relative_to(root)
    source = file.read_text(encoding="utf-8")
    for module in pattern.findall(source):
        imports += 1
        if not root.joinpath(*module.split(".")).with_suffix(".lean").is_file():
            missing.append((relative, module))
    new_proof = ("PaperI" in relative.parts or relative.name in {"PaperI.lean", "RevisedPaperI.lean"})
    for line, content in enumerate(source.splitlines(), 1):
        if content.strip() in {"sorry", "admit"}:
            admissions.append((relative, line))
            if new_proof:
                introduced.append((relative, line))
        if new_proof and re.match(r"^\s*(?:public )?axiom\s", content):
            introduced.append((relative, line))

print(f"Lean files: {len(files)}")
print(f"Project import references: {imports}")
print(f"Missing project imports: {len(missing)}")
print(f"Proof admissions: {len(admissions)}")
print(f"Proof admissions and axioms in the new modules: {len(introduced)}")
for relative, module in missing:
    print(f"{relative}: missing {module}")
for relative, line in introduced:
    print(f"{relative}:{line}: new admission or axiom")
sys.exit(bool(missing or introduced))
