# Provenance

Mathematical authors: **Wen Chang and Quanyu Tang**. Primary source: their
unpublished manuscript *Infinitely many Auslander–Reiten components over
perfect fields*, theorem `thm:main`, SHA-256
`698b9bfe948d1f84fbe37d25d82a6526589671a5b7a524ea8231922a65f3b23f`.
The manuscript itself is excluded. The same main theorem is publicly stated
as Theorem 1.2 of Wen Chang and Quanyu Tang's
*Infinitely many components in Auslander–Reiten quivers of
representation-infinite algebras over perfect fields*:
https://arxiv.org/html/2607.24466v2
The expanded input and the public paper are not claimed to have identical
proof text. The authors have authorized public publication of the Lean source.

The C3 and Tau Ceti source closure continues the authors' prior local
formalization. Existing source notices identify earlier Codex assistance and
Tau Ceti contributions; they have not been rewritten to attribute that earlier
work to Doubao. `verification/module-origins.json` records file hashes and
whether files differ from the prior local development.

Doubao-assisted continuation supplied the affine-cokernel coefficient/twist
argument, the regular Kronecker presentation and image-cokernel bridge, the
unconditional final assembly, version compatibility proofs and the release
checks/documentation. No Codex proof-generation session was run for this
continuation. The exact model identity of historical contributions is not
reconstructed; authorship and AI assistance are distinct.

The general embedding is imported from Haruhisa Enomoto's public Apache-2.0
library, pinned to `5aa8d0c033014aa2d73fe5d6306d6e6d4edbb14f`:
https://github.com/haruhisa-enomoto/third-brauer-thrall-conjecture
Its principal export is `LargeIndecomposable.theoremA`; reference paper:
https://arxiv.org/abs/2611.06325v1
The library contains substantive Bongartz embedding machinery. We neither
claim to have authored it nor replace it with a new axiom. Its own provenance,
licenses and notices remain in the pinned Git dependency.

Tau Ceti modules retain copyright and module adaptation notices. The 133
vendored modules originate at immutable upstream commit
`83769e442d55cda9d85b3927a93b286831c595ff`:
https://github.com/TauCetiProject/TauCeti/tree/83769e442d55cda9d85b3927a93b286831c595ff

`verification/vendor-tauceti.json` distinguishes each file's verified upstream
SHA-256, initial local adaptation SHA-256 and current release SHA-256. All 133
upstream hashes were rechecked against that commit fetched using GitHub CLI;
all initial hashes were checked against the preserved prior sources. The
initial adaptation modified two files, and eight files were subsequently
ported to the release's pinned Mathlib. These historical revision fields are
not dependency pins; the actual pins are in `lake-manifest.json`.

`verification/module-origins.json` remains the complete 210-module release
inventory, not a substitute for the upstream revision record. Source hash
checks do not constitute an independent mathematical review. The proof
closure of the advertised final result is checked by the axiom audit and
independent kernels. No claim is made that every declaration in the entire
upstream Tau Ceti repository was audited.

Checks made by the same assisting agent are self-review, not independent
expert review. No human line-by-line review or Palomar registration is claimed.
