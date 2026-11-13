module

public import C3PerfectField.ScalarExtensionRadicalSquares

/-!
Manuscript `cor:irr-base`. Canonical scalar extension of a subquotient
is obtained by restricting the Hom equivalence to the radical and then
passing to the quotient by its actual radical square.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v w z

section Subquotients

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  {V : Type w} {U : Type z} [AddCommGroup V] [Module k V]
  [AddCommGroup U] [Module K U]
  (p q : Submodule k V) (p' q' : Submodule K U)
  (e : (K ⊗[k] V) ≃ₗ[K] U)
  (hp : (p.baseChange K).map e.toLinearMap = p')
  (hq : (q.baseChange K).map e.toLinearMap = q')

/-- Restriction of an ambient canonical tensor equivalence to a subspace. -/
def scalarExtensionSubspaceEquiv : (K ⊗[k] p) ≃ₗ[K] p' :=
  (Submodule.toBaseChange.toLinearEquiv K p).trans
    (e.ofSubmodules (p.baseChange K) p' hp)

/-- Its underlying ambient map is exactly extension of the subspace inclusion. -/
theorem scalarExtensionSubspaceEquiv_subtype :
    p'.subtype ∘ₗ (scalarExtensionSubspaceEquiv p p' e hp).toLinearMap =
      e.toLinearMap ∘ₗ p.subtype.baseChange K := by
  ext x
  rfl

/-- The restricted equivalence uses the canonical tensor inclusion formula. -/
theorem scalarExtensionSubspaceEquiv_tmul_val (c : K) (x : p) :
    (scalarExtensionSubspaceEquiv p p' e hp (c ⊗ₜ[k] x) : U) =
      e (c ⊗ₜ[k] x.val) := rfl

include hq in
/-- Subspace restriction commutes with scalar extension of the denominator. -/
theorem scalarExtensionSubquotient_denominator_comap :
    (q'.comap p'.subtype).comap
      (scalarExtensionSubspaceEquiv p p' e hp).toLinearMap =
        (q.comap p.subtype).baseChange K := by
  have hq' : q'.comap e.toLinearMap = q.baseChange K := by
    rw [← hq]
    exact Submodule.comap_map_eq_of_injective e.injective _
  rw [← Submodule.comap_comp, scalarExtensionSubspaceEquiv_subtype,
    Submodule.comap_comp, hq', ← scalarExtension_comap]

/-- Canonical scalar extension of an arbitrary subquotient. -/
def scalarExtensionSubquotientEquiv :
    (K ⊗[k] (p ⧸ q.comap p.subtype)) ≃ₗ[K] (p' ⧸ q'.comap p'.subtype) := by
  let r := scalarExtensionSubspaceEquiv p p' e hp
  have hQ : ((q.comap p.subtype).baseChange K).map r.toLinearMap =
      q'.comap p'.subtype := by
    rw [← scalarExtensionSubquotient_denominator_comap p q p' q' e hp hq]
    exact Submodule.map_comap_eq_of_surjective r.surjective _
  exact (scalarExtensionQuotientEquiv (K := K) (q.comap p.subtype)).symm.trans
    (Submodule.Quotient.equiv _ _ r hQ)

/-- The subquotient equivalence is induced by the original canonical Hom map. -/
theorem scalarExtensionSubquotientEquiv_tmul (c : K) (x : p) :
    scalarExtensionSubquotientEquiv p q p' q' e hp hq
        (c ⊗ₜ[k] (q.comap p.subtype).mkQ x) =
      (q'.comap p'.subtype).mkQ (scalarExtensionSubspaceEquiv p p' e hp (c ⊗ₜ[k] x)) := by
  rw [← scalarExtensionQuotientEquiv_mk (q.comap p.subtype) c x]
  simp only [scalarExtensionSubquotientEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rfl

end Subquotients

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]
  (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N]

/-- The actual radical spaces are identified by the canonical Hom map. -/
def radicalScalarExtensionEquiv :
    (K ⊗[k] radicalSubmodule (k := k) M N) ≃ₗ[K]
      radicalSubmodule (k := K)
        (scalarExtensionObject (k := k) (K := K) M)
        (scalarExtensionObject (k := k) (K := K) N) :=
  scalarExtensionSubspaceEquiv _ _
    (moduleHomScalarExtensionEquiv (k := k) (K := K) M N)
    (algebraicClosure_radicalSubmodule_scalarExtension_map M N)

/-- Manuscript `cor:irr-base`, on the exact radical/radical-square quotients. -/
def irreducibleScalarExtensionEquiv :
    (K ⊗[k] IrreducibleSpace (k := k) M N) ≃ₗ[K]
      IrreducibleSpace (k := K)
        (scalarExtensionObject (k := k) (K := K) M)
        (scalarExtensionObject (k := k) (K := K) N) :=
  scalarExtensionSubquotientEquiv _ _ _ _
    (moduleHomScalarExtensionEquiv (k := k) (K := K) M N)
    (algebraicClosure_radicalSubmodule_scalarExtension_map M N)
    (algebraicClosure_radicalSquareSubmodule_scalarExtension_map M N)

/-- Scalar extension preserves the dimension of the actual irreducible space. -/
theorem finrank_irreducibleSpace_scalarExtension :
    Module.finrank K (IrreducibleSpace (k := K)
      (scalarExtensionObject (k := k) (K := K) M)
      (scalarExtensionObject (k := k) (K := K) N)) =
        Module.finrank k (IrreducibleSpace (k := k) M N) :=
  (irreducibleScalarExtensionEquiv M N).symm.finrank_eq.trans finrank_scalarExtension

/-- Nonzero irreducible spaces are preserved and reflected by scalar extension. -/
theorem nontrivial_irreducibleSpace_scalarExtension_iff :
    Nontrivial (IrreducibleSpace (k := K)
      (scalarExtensionObject (k := k) (K := K) M)
      (scalarExtensionObject (k := k) (K := K) N)) ↔
        Nontrivial (IrreducibleSpace (k := k) M N) := by
  have hs := (irreducibleScalarExtensionEquiv M N).toEquiv.subsingleton_congr.symm.trans
    (scalarExtension_subsingleton_iff (k := k) (K := K)
      (V := IrreducibleSpace (k := k) M N))
  simpa only [not_subsingleton_iff_nontrivial] using not_congr hs

end

end C3PerfectField
