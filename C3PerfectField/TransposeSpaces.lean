module

public import C3PerfectField.MinimalProjectivePresentations
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The vector-space cokernel of the dual presentation map and its field dual.
For the regular module `A^1`, these are the underlying vector spaces in
manuscript `lem:transpose-bound`. The module action, independence of the
chosen presentation, and almost split sequence identification are separate
representation-theoretic obligations. `TransposeModules.lean` now supplies
the actual module action and its dimension bound; independence and the
almost split identification remain open.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory
open scoped ModuleCat

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
variable {X : FiniteModule k A}

namespace MinimalProjectivePresentation

/-- The actual cokernel vector space of precomposition with the
presentation differential. -/
abbrev transposeSpaceAt (T : MinimalProjectivePresentation X) (V : FiniteModule k A) :=
  (T.P₁.val ⟶ V.val) ⧸ LinearMap.range (Linear.leftComp k V.val T.differential)

instance finite_transposeSpaceAt (T : MinimalProjectivePresentation X)
    (V : FiniteModule k A) : Module.Finite k (T.transposeSpaceAt V) := by
  let : Module.Finite k (T.P₁.val ⟶ V.val) := finite_module_hom T.P₁ V
  unfold transposeSpaceAt
  infer_instance

/-- Taking the quotient cannot increase dimension. -/
theorem finrank_transposeSpaceAt_le [FiniteDimensional k A]
    (T : MinimalProjectivePresentation X) (V : FiniteModule k A) :
    Module.finrank k (T.transposeSpaceAt V) ≤
      Module.finrank k V.val * Module.finrank k A * Module.finrank k X.val := by
  let : Module.Finite k (T.P₁.val ⟶ V.val) := finite_module_hom T.P₁ V
  exact (Submodule.finrank_quotient_le
    (LinearMap.range (Linear.leftComp k V.val T.differential))).trans
      (T.finrank_hom_P₁_le V)

/-- The field dual of this cokernel, before equipping it with its
representation-theoretic module action. -/
abbrev dualTransposeSpaceAt (T : MinimalProjectivePresentation X) (V : FiniteModule k A) :=
  Module.Dual k (T.transposeSpaceAt V)

instance finite_dualTransposeSpaceAt (T : MinimalProjectivePresentation X)
    (V : FiniteModule k A) : Module.Finite k (T.dualTransposeSpaceAt V) := by
  unfold dualTransposeSpaceAt
  infer_instance

theorem finrank_dualTransposeSpaceAt_le [FiniteDimensional k A]
    (T : MinimalProjectivePresentation X) (V : FiniteModule k A) :
    Module.finrank k (T.dualTransposeSpaceAt V) ≤
      Module.finrank k V.val * Module.finrank k A * Module.finrank k X.val := by
  rw [Subspace.dual_finrank_eq]
  exact T.finrank_transposeSpaceAt_le V

end MinimalProjectivePresentation

/-- The regular module represented in the target universe as `A^1`.
Its field dimension is exactly that of `A`. -/
def regularFiniteModule [FiniteDimensional k A] : FiniteModule k A :=
  ⟨finiteFreeModule k A 1, inferInstance⟩

theorem finrank_regularFiniteModule [FiniteDimensional k A] :
    Module.finrank k (regularFiniteModule (k := k) (A := A)).val =
      Module.finrank k A := by
  exact (finrank_finiteFreeModule (k := k) (A := A) 1).trans (Nat.one_mul _)

/-- The `d^2 dim_k X` estimate for the underlying dual-transpose vector
space, using actual finite minimal presentations and the regular module.
No almost split existence statement is assumed or concluded. -/
theorem finrank_dualTranspose_regular_le [FiniteDimensional k A]
    (T : MinimalProjectivePresentation X) :
    Module.finrank k (T.dualTransposeSpaceAt (regularFiniteModule (k := k) (A := A))) ≤
      (Module.finrank k A) ^ 2 * Module.finrank k X.val := by
  simpa only [finrank_regularFiniteModule, pow_two] using
    T.finrank_dualTransposeSpaceAt_le (regularFiniteModule (k := k) (A := A))

end C3PerfectField
