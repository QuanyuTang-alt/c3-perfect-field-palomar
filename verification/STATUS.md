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

## Important qualification

Comparator and the independent checkers were actually run on macOS with
`--inadvisably-no-sandbox`, because bubblewrap requires Linux namespaces.
They checked the generated exports and returned acceptance, but this is **not**
a sandboxed Palomar verification. The output warning is retained in the evidence.
No independent human expert review or automated Palomar acceptance is claimed.

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

**Palomar submission/registration: NOT PERFORMED.** Public GitHub publication
is authorized; registry submission is still a separate action. No independent
human expert review or Palomar acceptance is claimed.

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
