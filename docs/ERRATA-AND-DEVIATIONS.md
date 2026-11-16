# Errata and deviations

This record distinguishes defects in the source from deliberate changes of
formal proof route or conventions. A supplied proof of a true source step is
a deviation, not a claim that the authors stated a false result. Counts are
entries, not occurrences. The primary source is the manuscript identified by
SHA-256 `698b9bfe948d1f84fbe37d25d82a6526589671a5b7a524ea8231922a65f3b23f`.
No source erratum affecting `thm:main` is claimed. Its proof uses only
`propext`, `Classical.choice` and `Quot.sound`.

| Source | Claimed errata | Deviations |
| --- | ---: | ---: |
| Chang–Tang manuscript, `thm:main` and its proof | 0 | 2 |
| Enomoto embedding export at the pinned revision | 0 | 0 |
| Total | 0 | 2 |

## Chang–Tang manuscript

### Errata

None claimed. This is not an exhaustive errata review of the entire manuscript.

### Deviations

1. **`ext:embedding`, algebraically closed proof.** Instead of reconstructing
   the full finite-free polynomial bimodule statement, the development uses the
   proved Kronecker representation embedding and its regular family. The
   explicit short exact presentation produces fixed finite modules and maps
   `f,g` with fibers `cokernel (f - lambda • g)`. Their indecomposability,
   parameter distinction and twist equivariance are proved. The family is
   sufficient for the original prime-period component argument. No change to
   the final hypotheses or conclusion. See `C3KroneckerPresentation.lean`,
   `C3KroneckerEmbedding.lean`, `C3PerfectField/MorphismCoefficientTwists.lean`
   and `C3Integration.lean`.
2. **`thm:main`, carriers and connectivity.** The final export puts `k` and `A`
   in the same arbitrary universe `u`. This is a size convention, not a finite
   cardinality restriction; usual fields and algebras are covered. The
   categorical module carrier is `Type u`. Undirected connectivity is encoded
   by a simple graph omitting loops, which do not change components. No separate
   universe-change equivalence theorem is advertised. Definitions appear
   literally in `C3PalomarSubmission/Challenge.lean` and `C3PerfectField/MainStatement.lean`.

## Enomoto embedding export

### Errata

None claimed; this repository does not independently review every source
statement of the embedding library.

### Deviations

None in the used export. The interface is `LargeIndecomposable.theoremA` at
commit `5aa8d0c033014aa2d73fe5d6306d6e6d4edbb14f`. Its finite-value, exactness,
indecomposability and isomorphism-reflection conclusions are consumed by
proved bridges. Stronger infinite-dimensional conclusions are not used.

## Scope and route

Perfect-field descent follows `cor:infinite-extension` and `prop:components`
via the algebraic closure, Galois summand transitivity and lifted paths.
Only the main theorem is the registry-facing result. The complete standalone
polynomial bimodule embedding, and every unused lemma or external theorem in
the manuscript, are not separately advertised as formalized.
