# Statement and definition self-audit

Target source: Chang–Tang manuscript, `thm:main`, lines 1701–1705 in the
provided revision, SHA-256
`698b9bfe948d1f84fbe37d25d82a6526589671a5b7a524ea8231922a65f3b23f`.
This record is self-review, not independent author or expert approval.

## Expanded binders of `PalomarC3.main_result`

| Binder | Bin | Mathematical source correspondence |
| --- | --- | --- |
| `k : Type u` | TYPING | the field's carrier |
| `A : Type u` | TYPING | the algebra's carrier |
| `[Field k]` | SOURCE | k is a field |
| `[Ring A]` | TYPING | unital associative algebra |
| `[Algebra k A]` | SOURCE | A is a k-algebra |
| `[PerfectField k]` | SOURCE | k is perfect |
| `[FiniteDimensional k A]` | SOURCE | A is finite-dimensional |
| `hA : InfiniteRepresentationType k A` | SOURCE | infinite representation type |

Counts: SOURCE 5, TYPING 3, STANDING 0, RULED 0, EXCESS 0. The predicate
`InfiniteRepresentationType` literally expands to `Infinite (ARVertex k A)`.
No nullary proposition package or hidden embedding/family premise appears.
The conclusion is `Infinite (ARGraph k A).ConnectedComponent`.

## Meaning-carrying definitions

* `FiniteModule`: actual `ModuleCat A` objects with finite k-module predicate.
* `IndecomposableModule`: such objects with categorical indecomposability;
  zero objects excluded. The bridge proves equivalence with the upstream
  nontrivial/no-complementary-submodules predicate.
* `isoSetoid`, `ARVertex`: the actual module-isomorphism quotient.
* `IsRadical`: every `id - f ≫ g` is invertible.
* `IsRadicalSquare`: arbitrary finite sums of pairs of radical maps factoring
  through arbitrary finite-dimensional modules, not a restricted chosen family.
* `HasARArrow`: radical element not in radical square.
* `ARArrow`: relation on actual isomorphism classes by representatives.
* `ARGraph`: symmetric adjacency from either arrow direction, distinct vertices;
  omitting loops does not affect connectedness.

All are literal definitions; there are no default branches standing in for
missing constructions. BODY_MATCH: OK; PUBLIC_CARRIER: OK;
WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL;
CHOICE_INDEPENDENCE: N/A for the literal definitions. Quotient representatives
used in proofs are justified by quotient soundness and actual isomorphism
invariance, not an assumption about abstract vertices.

## Exact consumption

`C3Integration.lean` applies the proved upstream theorem to the proved
representation-infinite bridge. It forms actual finite images of the two
fixed Kronecker presentation modules, proves fiber indecomposability and
parameter reflection, then applies the affine-cokernel component argument.
The perfect-field theorem supplies algebraic-closure infinite representation
type and applies the proved scalar-extension component descent. The short
Solution wrapper consumes this complete theorem at the exact source type.

## Mechanical evidence and boundaries

The integration `main-audit.log` checks declaration kind, the independently
written exact-type application and the axiom closure of four substantive
exports. All returned only `propext`, `Classical.choice`, `Quot.sound`.
The shipped `verification/Audit.lean` reruns these checks and the registry
wrapper on the final release tree. See `verification/STATUS.md` for actual
execution status; compilation alone is not source fidelity.

The final theorem uses a common arbitrary universe for k and A; no separate
universe-lifting equivalence is advertised. The Challenge definitions are
independent literal copies, imported only from Mathlib. Comparator has no
definition holes, so reachable definitions must match in body as well as type.
The only `sorry` is Challenge's deliberate theorem hole; Solution never imports
Challenge. This does not certify every unused manuscript lemma or independent
human review.
