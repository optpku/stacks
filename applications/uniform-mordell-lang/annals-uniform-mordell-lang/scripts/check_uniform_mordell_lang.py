#!/usr/bin/env python3
"""Build both independent Lake repositories and check UniformMordellLang's data.

Run in a shell with Lake/Elan on PATH:
    python3 scripts/check_uniform_mordell_lang.py
The foundations checkout is the relative path declared in lakefile.toml.
Proof sorries remain allowed; data sorries and unknown audit roots are rejected.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "lake-manifest.json").read_text())
    dependency = next(r for r in manifest["packages"]
                      if r["name"] == "JacobianFoundations")
    assert dependency["type"] == "path"
    foundations = (root / dependency["dir"]).resolve()
    work = root / ".work" / "validation"
    temp = work / "tmp"
    temp.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    # Let Lake determine every import path; an inherited manual LEAN_PATH must
    # not substitute cached artifacts from the previous 4.32 experiment.
    env.pop("LEAN_PATH", None)
    env.update(TMPDIR=str(temp), TMP=str(temp), TEMP=str(temp),
               XDG_CACHE_HOME=str(work / "cache"))
    report = {"success": False, "checks": [], "repositories": {}}

    def run(name, argv, cwd=root, expected_error=None):
        proc = subprocess.run(argv, cwd=cwd, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = work / (name + ".log")
        log.write_text(proc.stdout)
        passed = (proc.returncode == 0 if expected_error is None else
                  proc.returncode != 0 and expected_error in proc.stdout)
        report["checks"].append({"name": name, "exit_code": proc.returncode,
                                 "passed": passed,
                                 "log": str(log.relative_to(root))})
        print(f"{name}: {'PASS' if passed else 'FAIL'}", flush=True)
        if not passed:
            print(proc.stdout[-12000:], flush=True)
            raise RuntimeError(name + " failed")
        return proc.stdout

    try:
        for label, repo in [("foundations", foundations), ("annals", root)]:
            report["repositories"][label] = {
                "path": str(repo),
                "toolchain": (repo / "lean-toolchain").read_text().strip(),
                "workspace_head": (lambda p: p.stdout.strip() if p.returncode == 0 else None)(
                    subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                                   text=True, capture_output=True)),
                "manifest_sha256": hashlib.sha256(
                    (repo / "lake-manifest.json").read_bytes()).hexdigest(),
            }
        assert (report["repositories"]["foundations"]["toolchain"] ==
                report["repositories"]["annals"]["toolchain"])
        expected_toolchain = "leanprover/lean4:v4.32.0"
        expected_mathlib = "81a5d257c8e410db227a6665ed08f64fea08e997"
        assert report["repositories"]["annals"]["toolchain"] == expected_toolchain
        for repo in [root, foundations]:
            pinned = json.loads((repo / "lake-manifest.json").read_text())
            assert next(p["rev"] for p in pinned["packages"]
                        if p["name"] == "mathlib") == expected_mathlib
        repository_root = root.parents[2]
        if (repository_root / "lean-toolchain").exists():
            assert (repository_root / "lean-toolchain").read_text().strip() == expected_toolchain
            pinned = json.loads((repository_root / "lake-manifest.json").read_text())
            assert next(p["rev"] for p in pinned["packages"]
                        if p["name"] == "mathlib") == expected_mathlib
        report["lean"] = run("toolchain", ["lake", "env", "lean", "--version"]).strip()
        run("foundations-build", ["lake", "--rehash", "build", "ReasLib", "JacobianFoundations"], cwd=foundations)
        run("annals-build", ["lake", "--rehash", "build"])
        run("reaslib-semantic-guards", ["lake", "env", "lean",
            "AnnalsChallenge/Tests/UniformMordellLangReasLib.lean"])
        # Re-execute the audit to collect its dependency counts even if Lake has
        # cached the successful test module from an earlier build.
        audit = run("data-audit", ["lake", "lean",
                    "AnnalsChallenge/Tests/UniformMordellLang.lean"])
        rows = re.findall(
            r"CENSUS (.*?): visited=(\d+); proofOnlyDeclarations=(\d+); "
            r"dataDeclarations=(\d+); dataHoles=(\d+)", audit)
        report["census"] = [dict(root=n, visited=int(v), proof_only_declarations=int(p),
                                  data_declarations=int(d), data_holes=int(h))
                            for n, v, p, d, h in rows]
        assert len(rows) == 6 and all(int(row[4]) == 0 for row in rows)
        fixtures = [
            ("reject-data-hole", "def forbiddenDataHole : Nat := by sorry\n"
             "#assert_no_data_sorries forbiddenDataHole\n",
             "Reachable non-Prop sorry holes: 1"),
            ("reject-nested-data-hole", "theorem nestedProofTypeHole : True :=\n"
             "  sorryAx (let n : Nat := sorryAx Nat false; True) false\n"
             "#assert_no_data_sorries nestedProofTypeHole\n",
             "Reachable non-Prop sorry holes: 1"),
            ("reject-unknown-root", "#assert_no_data_sorries absentAuditRoot\n",
             "Unknown audit root: absentAuditRoot"),
            ("allow-proof-hole", "theorem deferredProof : True := by sorry\n"
             "#assert_no_data_sorries deferredProof\n", None),
        ]
        for name, body, expected in fixtures:
            source = work / (name + ".lean")
            source.write_text("import AnnalsChallenge.Tests.UniformMordellLang\n" + body)
            run(name, ["lake", "lean", str(source)], expected_error=expected)
        sources = {}
        for repo_label, repo in [("annals", root), ("foundations", foundations)]:
            for pattern in (["AnnalsChallenge/Definitions/AlgebraicJacobian.lean",
                             "AnnalsChallenge/Definitions/Jacobian/*.lean",
                             "AnnalsChallenge/AnnalsOfMathematics/*UniformMordellLang.lean",
                             "AnnalsChallenge/Tests/*UniformMordellLang*.lean"]
                            if repo_label == "annals" else ["JacobianFoundations/*.lean"]):
                for path in repo.glob(pattern):
                    sources[repo_label + "/" + str(path.relative_to(repo))] = (
                        hashlib.sha256(path.read_bytes()).hexdigest())
        report["source_sha256"] = sources
        # Record the actual extracted library sources, not only the original
        # provenance hashes: semantic repairs may change a ReasLib definition.
        report["reaslib_source_sha256"] = {
            str(path.relative_to(foundations)).removesuffix(".lean").replace("/", "."):
                hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted((foundations / "ReasLib").rglob("*.lean"))
        }
        report["semantic_review"] = "../INDEPENDENT_REVIEW.md"
        report["proofs_deferred"] = True
        report["success"] = True
    finally:
        (work / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Report:", work / "validation.json", flush=True)


if __name__ == "__main__":
    main()
