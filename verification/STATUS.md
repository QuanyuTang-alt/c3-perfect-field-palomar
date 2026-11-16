# Verification and release status

## Proved result

`C3PerfectField.mainTheorem` and `PalomarC3.main_result` prove:
for a perfect field k and a finite-dimensional unital associative k-algebra A
of infinite representation type, the actual Auslander–Reiten graph has
infinitely many connected components. No representation embedding, family,
classification or literature hypothesis is assumed by the final theorem.
The theorem is unconditional in its mathematical hypotheses; its only axioms
are Lean's standard classical three.

## Executed checks on the delivered source

| Check | Result | Evidence |
| --- | --- | --- |
| Source-only directory with freshly fetched pinned public Git dependencies | PASS | `fresh-build.log`, `fresh-build-resume.log` |
| Complete build of Solution and Challenge | PASS, 10351 jobs | `fresh-build-resume.log` |
| Rebuild after final source adaptation notices | PASS, 10351 jobs | `final-build.log` |
| Exact theorem type and declaration kind | PASS | `final-audit.log` |
| Five exported theorem axiom closures | PASS: propext, Classical.choice, Quot.sound only | `final-audit.log` |
| Comparator statement and reachable-definition bodies | PASS; no definition holes | `final-comparator-result.txt` |
| Lean default kernel replay | PASS | `final-comparator-result.txt` |
| NanoDa independent replay | PASS | `final-comparator-result.txt` |
| con-ron independent replay | PASS, 104382 declarations accepted | `final-comparator-result.txt` |
| 210 local Lean files: module headers, length, holes, pins, checksums, private-reference scan | PASS | `final-integrity.txt` |
| Official formalization.yaml v0.4 schema | PASS | `final-metadata.txt`, stored schema |
| README theorem text matches the complete Solution declaration | PASS | direct substring check |
| Shell script syntax and CI YAML parse | PASS | local syntax/parser checks |

The source-only build began with empty project and embedding-library build
artifacts. Mathlib cache artifacts for the exact pin were obtained through its
normal cache command. Dependencies are real independently fetched directories,
not paths or symlinks to the earlier development project. An interrupted first
build was resumed without removing or altering dependency artifacts; the full
build and final rebuild both exited 0.

All 210 local Lean modules are in the Solution/Challenge/Audit source import
closure. The one intentional theorem `sorry` in Challenge is not imported by
Solution and does not occur in its proof dependency closure. Warnings from the
pinned upstream library and stylistic local notices are visible and nonfatal;
proof/build/audit/checker failures remain fatal.

## Commit-bound Linux CI evidence

The original public commit `131da532f985913d25ec6c815a98153c4aa8d200` has
**two actual successful GitHub Actions runs**:

* [Lean build, metadata, integrity and axiom audit](https://github.com/QuanyuTang-alt/c3-perfect-field-palomar/actions/runs/43477729972):
  full 10351-job build and the five advertised theorem axiom closures passed.
* [Comparator and independent kernels](https://github.com/QuanyuTang-alt/c3-perfect-field-palomar/actions/runs/43477729917):
  genuine Linux bubblewrap isolation; declaration/definition comparison and
  con-ron (104382 declarations), NanoDa and Lean default replay all passed.

These are immutable-revision workflow results, not claims inferred from README
or local saved logs. Later commits must be checked against their own workflow
runs. The documentation/provenance revision does not change mathematical
statements or proofs; its current status is shown by the linked README badges
and GitHub Actions. Do not treat these old run links as evidence that an arbitrary
later revision passed.

## Module-layout repair checks

After the Palomar provenance failure described below, the new registry modules
were validated locally with the pinned toolchain:

* `lake build +C3PalomarSubmission.Solution +C3PalomarSubmission.Challenge`:
  PASS, 10351 build jobs; both newly named modules compiled.
* `lake env lean verification/Audit.lean`: PASS, exact target type and all five
  advertised exports use only `propext`, `Classical.choice`, `Quot.sound`.
* `python3 scripts/check_integrity.py`: PASS, 210 module sources; definition
  identity, proof-hole quarantine, checksums and provenance coverage checked.
* `python3 scripts/test_module_layout.py`: PASS, both directory and Lean-file
  collisions rejected, missing dependency rejected, restored layout accepted.
* Metadata schema plus configured module/file alignment, README theorem
  substring check, shell syntax, CI YAML parse and Git whitespace checks: PASS.
* All ten real dependency roots match their exact manifest Git revisions, and
  none contains a top-level `C3PalomarSubmission` or `C3PalomarSubmission.lean`.
* Challenge and Solution are byte-identical to their original files; all other
  mathematical Lean sources and dependency pins are unchanged. Only the audit
  module's import line changes.

These local checks are not a new Palomar submission. Both enabled hosted
workflows must be checked on the repaired commit before resubmitting; they
rerun the new layout regression and real dependency audit, and the comparator
workflow replays the renamed solution in all three kernels.

## Historical local checks and review boundary

The saved local Comparator/checker records were obtained on macOS with
`--inadvisably-no-sandbox`, because bubblewrap requires Linux namespaces. That
local evidence is not a sandboxed run; the commit-bound Linux runs above supply
the previously missing isolation evidence. Historical logs and source hashes
refer to the snapshots named when recorded, rather than being silently relabeled
as the later documentation revision.

No independent human expert review or automated Palomar acceptance is claimed.
A separate LLM review supplied by the maintainer concerns the original public
commit; its identity, scope and limitations are recorded in `docs/REVIEW-NOTES.md`.

The complete proof uses Enomoto's proved pinned representation-embedding
library. Its embedding theorem is an ordinary proof dependency, not a new
axiom, and is credited in the README/metadata. The original manuscript's
stronger polynomial bimodule external statement is not independently
advertised; the sufficient affine-presentation route is fully proved.

## GitHub publication and registry status

The authors have now authorized a **public** repository under
`QuanyuTang-alt/c3-perfect-field-palomar`. The same mathematical theorem is
public as Theorem 1.2 of https://arxiv.org/html/2607.24466v2.
This new authorization supersedes the earlier private-only preparation.
The original TeX remains excluded.

The two pinned workflows are enabled for pushes and pull requests to `main`,
and manual dispatch. Their current hosted status must be read from GitHub
Actions, not inferred from this local audit. The build/audit workflow performs
source and metadata checks; the comparator workflow uses genuine Linux
bubblewrap and Lean, NanoDa and con-ron. Local macOS success does not by itself
establish sandboxed Linux success.

**Palomar submission status:** the maintainer submitted commit
`186c74eee4e960e1d0b6621e0e9310156d91bbe2`. Its
[mechanical run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/43906636480)
failed with diagnostic `challenge.module_root_shadowed`: Verso would find
`Challenge.lean` in the `large_indecomposable` dependency rather than the local
statement. The report lists this one repository repair. It did not reach
independent kernel checks (`kernels` is empty); the earlier successful project
CI is separate evidence and is not Palomar acceptance.

The repaired modules are `C3PalomarSubmission.Challenge` and
`C3PalomarSubmission.Solution`. Both are moved byte-for-byte, so the theorem and
its meaning are unchanged. The new top-level directory is absent from all
pinned dependencies. `scripts/check_integrity.py` now rejects module-root
collisions for both registry modules, besides its existing source checks.
See `docs/PALOMAR-MODULE-LAYOUT.md` for the precise changes and regression test.

The repaired commit needs a **new submission** by the maintainer. No new
submission or registration was performed by the assisting agent; no human
expert review or Palomar acceptance is claimed.

The local source and proof checks above remain valid. GitHub publication does
not alter the theorem, its definitions, dependency pins or the axiom policy.

## Contents and privacy

Authors are Wen Chang and Quanyu Tang in the first lines of README and in
metadata. New continuation assistance is attributed to Doubao, not a fictitious
Codex generation run. Earlier Codex and third-party notices remain where they
apply. The package contains no original TeX, manuscript PDF, credentials,
private development history, absolute dependency paths, copied `.lake` caches
or toolchain installation. The code license does not license the manuscript.

Reproduce the build, axiom/integrity/schema audits and Linux comparison using
README commands. The exact Lean sources are bound by `SHA256SUMS`.
