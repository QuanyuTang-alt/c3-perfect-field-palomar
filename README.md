# Infinite Auslander–Reiten components over perfect fields

**Authors: Wen Chang and Quanyu Tang**

[![Lean verification](https://github.com/QuanyuTang-alt/c3-perfect-field-palomar/actions/workflows/lean.yml/badge.svg)](https://github.com/QuanyuTang-alt/c3-perfect-field-palomar/actions/workflows/lean.yml)
[![Comparator and kernels](https://github.com/QuanyuTang-alt/c3-perfect-field-palomar/actions/workflows/comparator.yml/badge.svg)](https://github.com/QuanyuTang-alt/c3-perfect-field-palomar/actions/workflows/comparator.yml)

## Mathematical result

Let `k` be a perfect field and `A` a finite-dimensional unital associative
`k`-algebra of infinite representation type. Then its Auslander–Reiten quiver
has infinitely many connected components.

The vertices are isomorphism classes of actual nonzero indecomposable
finite-dimensional left `A`-modules. Arrows are detected by nonzero radical
modulo radical square; connectivity is undirected, with loops discarded.
No algebraic-closedness, countability, splitness, representation embedding,
parameter family, or additional literature hypothesis is assumed by the final theorem.

The complete proved registry-facing declaration in `C3PalomarSubmission/Solution.lean` is

```lean
theorem main_result (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [PerfectField k] [FiniteDimensional k A]
    (hA : C3PerfectField.InfiniteRepresentationType k A) :
    Infinite (C3PerfectField.ARGraph k A).ConnectedComponent :=
  C3PerfectField.mainTheorem k A hA
```

It lives in namespace `PalomarC3`. The substantive theorem is
`C3PerfectField.mainTheorem` in `C3Integration.lean`, not the deliberate
statement hole in `C3PalomarSubmission/Challenge.lean`.

## What has been formalized

* Actual finite-dimensional module categories, indecomposable isomorphism
  classes, categorical radical and radical square, and the AR graph.
* Almost-split/projective-cover arguments supplying local weighted-neighbor
  bounds, and the graph-theoretic prime-period propagation argument.
* Finitely generated coefficient fields, semilinear twists, large prime
  automorphism orbits, and an affine-cokernel parameter family argument.
* The regular Kronecker family `(k,k;1,lambda)`, its short exact presentation,
  and its image under an actual representation embedding.
* Scalar-extension Hom/radical comparison, indecomposable-summand descent,
  Galois transitivity, path lifting, and the perfect-field conclusion.

The general representation embedding is supplied by the **proved**, pinned
`LargeIndecomposable.theoremA` in Haruhisa Enomoto's
[third-brauer-thrall-conjecture](https://github.com/haruhisa-enomoto/third-brauer-thrall-conjecture)
repository. Its substantial Bongartz machinery is not attributed to this
repository's authors. It is a proof dependency, not an added axiom or a
hypothesis of our theorem. The bridge proves the equivalence of the two
indecomposability/representation-type conventions before applying it.

## Proof route and source

The mathematical result is publicly available as **Theorem 1.2** of
[arXiv:2607.24466v2](https://arxiv.org/html/2607.24466v2), Wen Chang and
Quanyu Tang, *Infinitely many components in Auslander–Reiten quivers of
representation-infinite algebras over perfect fields*.

This development was based on the authors' expanded formalization-oriented
manuscript *Infinitely many Auslander–Reiten components over perfect fields*,
theorem `thm:main`, source revision identified by SHA-256
`698b9bfe948d1f84fbe37d25d82a6526589671a5b7a524ea8231922a65f3b23f`.
The public paper and the expanded input share the main mathematical theorem;
we do not claim their proof texts are byte-identical. The original TeX,
manuscript text and private development history are not distributed here.

The perfect-field descent follows the manuscript. In the algebraically closed
case we obtain the sufficient parameter family as
`cokernel (f - lambda • g)` from the regular Kronecker short exact sequence.
This replaces construction of the manuscript's stronger finite-free polynomial
bimodule embedding by an equivalent sufficient presentation route. It does
**not** claim to formalize every external theorem in its full standalone form.

The helper modules `PerfectFieldReduction.lean`,
`AlgebraicallyClosedComponents.lean`, and `PolynomialRepresentationEmbeddings.lean`
retain the alternative polynomial-tensor interface and explicit conditional
premises. Their existence claims are not used as assumptions of the final
proof. The unconditional entry is `C3Integration.lean`, with the proved
Kronecker embedding and affine-cokernel route described above.

## AI assistance and review

The mathematical result and original informal proof are by Wen Chang and
Quanyu Tang. This continuation, including the affine-cokernel bridge,
Kronecker presentation, final assembly, compatibility repairs and packaging,
was developed with **Doubao (豆包)** from the authors' original informal proof
and the prior local Lean development, using compiler feedback and axiom audits.
It was not generated by a Codex session in this continuation. Existing Codex
notices in reused local code and third-party copyright notices are retained;
a complete model-by-model history of earlier code has not been reconstructed.
No independent human expert review or Palomar acceptance is claimed.
The maintainer supplied a separate LLM review of the original public commit;
its unspecified identity, stated checks and limitations, and the resulting
documentation repairs are recorded in [Review notes](docs/REVIEW-NOTES.md).
See also `docs/PROVENANCE.md` and `docs/STATEMENT-AUDIT.md`.

## Reproduce

Pinned Lean: `leanprover/lean4:v4.35.0-rc3`.
Pinned Mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e`.
Pinned embedding library: `5aa8d0c033014aa2d73fe5d6306d6e6d4edbb14f`.
All dependencies are public Git dependencies; the manifest records transitive pins.

With Git, elan and Python 3 installed, in the repository root run

```sh
lake env lean --version
lake exe cache get
lake build +C3PalomarSubmission.Solution +C3PalomarSubmission.Challenge
python3 scripts/check_integrity.py
python3 scripts/test_module_layout.py
python3 -m pip install -r scripts/requirements-validation.txt
python3 scripts/check_metadata.py
lake env lean verification/Audit.lean
```

Warnings are reported but nonfatal; a failed build, integrity check, axiom audit
or checker remains fatal. Do not change pins to make a check pass.
For the registry-style comparison on Linux (bubblewrap required) run

```sh
bash scripts/verify-comparator.sh
```

The script compares the independent Mathlib-only Challenge to Solution,
checks the standard axiom allowlist, and replays through Lean, NanoDa and con-ron.
It never imports `C3PalomarSubmission.Challenge` into the proof. The one deliberate `sorry` in
Challenge is the statement hole, not a proof dependency. The substantive source
and Solution have no `sorry`, `admit`, `native_decide` or custom axiom.

## Verification and publication status

See `verification/STATUS.md` for the precise local checks and qualifications.
The authors have authorized **public GitHub publication** of this source package.
The two GitHub Actions workflows run on pushes and pull requests to `main`,
and can be started manually. Their badges link to the actual current results;
local checks and workflow files alone are not evidence of a green hosted run.
A submission of commit `186c74eee4e960e1d0b6621e0e9310156d91bbe2` failed
Palomar's module-source provenance check because the dependency also contains
a root `Challenge.lean`. The registry-facing modules are now
`C3PalomarSubmission.Challenge` and `C3PalomarSubmission.Solution`, under a
top-level directory absent from all pinned dependencies. The statement,
definitions and proof are unchanged. See
[Module-layout repair](docs/PALOMAR-MODULE-LAYOUT.md).

A new Palomar submission must use the full commit SHA of this repaired revision.
The root project layout and `comparator.json` metadata/configuration paths are
unchanged; the dotted module names are configured inside that JSON file.
No new submission has been made by the assisting agent, and no registration or
Palomar acceptance is claimed.

## Files

* `C3Integration.lean`: unconditional final proof assembly.
* `C3PerfectField/`: substantive AR, graph, field and descent arguments.
* `C3Kronecker*.lean`: regular family and affine short exact presentation.
* `TauCeti/`: dependency closure from the prior development, with
  existing copyright and adaptation notices retained.
* `C3PalomarSubmission/Challenge.lean`: small, independently readable statement and definitions.
* `C3PalomarSubmission/Solution.lean`, `comparator.json`: proved comparison target and configuration.
* `formalization.yaml`, `CITATION.cff`, `LICENSE`: metadata, authors and licensing.
* `verification/Audit.lean`, `scripts/`: reproducible integrity/axiom/comparison checks.
* `verification/vendor-tauceti.json`: verified fixed upstream revision and the
  upstream, initial adaptation and current hashes for all 133 vendored modules.
  `verification/module-origins.json` is the separate full local source inventory.
* `.github/workflows/`: separate build/audit and comparator/kernel workflows.

## Errata and deviations

[Errata and deviations](docs/ERRATA-AND-DEVIATIONS.md) records **0 claimed source
errata and 2 deviations** for the primary manuscript: the affine-presentation
proof route, and the shared universe/undirected loop-free graph convention.
The cited upstream embedding export is used as proved; no claim is made about
errata in that paper. No mathematical premise is added to the final theorem.

## License

Lean source and accompanying repository documentation: Apache-2.0. This does
not grant a license to the excluded manuscript. Reused Tau Ceti and upstream
material keeps its own attribution; see `NOTICE` and `docs/PROVENANCE.md`.
