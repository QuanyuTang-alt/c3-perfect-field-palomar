# Review feedback and submission-facing corrections

## Review supplied by the maintainer

The maintainer supplied a review from another LLM of immutable commit
`131da532f985913d25ec6c815a98153c4aa8d200`. The reviewer's model and identity
were not supplied. This repository records it as **maintainer-provided LLM
feedback**, not an authenticated independent expert review or a Palomar verdict.

The review reports checking the public paper's Theorem 1.2 and module/radical
conventions, the final Lean statement and definition bodies, the actual
Kronecker/affine-cokernel assembly, perfect-field descent and upstream interface.
It reports running integrity, metadata, definition-copy and import-closure checks.
Its full-build and three-kernel conclusions were obtained by reading the
commit's actual Linux CI logs, **not** a new full local rebuild by that reviewer.
It reports finding no substantive semantic hole, extra premise or unfinished
proof entering the final theorem. No line-by-line review of all upstream
proofs or guarantee of absolute correctness is claimed.

## Findings and dispositions

| Finding | Correction | Effect on mathematics |
| --- | --- | --- |
| Polynomial-route comments imply the main theorem is still incomplete | Clarified supplied-embedding helpers in `PerfectFieldReduction.lean`, `AlgebraicallyClosedComponents.lean`, and `PolynomialRepresentationEmbeddings.lean`; all point to the unconditional `C3Integration.lean` entry | None; conditional helper signatures remain conditional |
| `AlmostSplitExistence.lean` names a missing upstream record | Added `verification/vendor-tauceti.json` after checking all 133 upstream hashes against the actual fixed GitHub revision; distinguish upstream, initial adaptation and release bytes | None; proof source and dependency pins unchanged |
| Other construction comments retain obsolete global-gap wording | Updated `AlmostSplitPredecessors.lean`, `TransposeModules.lean` and `ComponentSeparation.lean` to name the proved providers/consumers | None; no proof text changed |
| A self-audit refers to a historical log by an unshipped name | Corrected references to the shipped audit evidence | None |
| Saved provenance hashes were not enforced by CI | Extended `scripts/check_integrity.py` to check exact inventories and release hashes, Challenge definition identity, and absence of Challenge from Solution's local import closure | Additional regression protection, not a substitute for kernel checking |
| Status text emphasizes historical macOS checks without fixed Linux CI links | Added a commit-bound record of both actual successful Linux workflows | Evidence clarification only |

The stronger standalone polynomial-bimodule existence statement is not newly
advertised as proved. The actual sufficient family is obtained from the proved
Kronecker embedding. No theorem premises, mathematical definitions, proof
bodies, imports, toolchain pins or dependency pins were changed by the comment
corrections.

## Reverification and submission boundary

The revision is rebuilt and axiom-audited locally, then pushed for both hosted
CI workflows. Use the **new revision's** full 40-character commit and verify its
own two successful runs; the earlier review is not automatically a review of
all later repository edits. `verification/STATUS.md` distinguishes old evidence
from current workflow results. Registration is not performed by this repair.

The primary target remains Theorem 1.2 of arXiv:2607.24466v2. This is not a claim
that every lemma or paragraph of that paper has been formalized separately.
