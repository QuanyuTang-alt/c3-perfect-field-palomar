module

public import C3PerfectField.ScalarExtensionHom
public import C3PerfectField.ScalarExtensionGalois
public import C3PerfectField.ARTwisting

/-!
Manuscript `lem:extended-fixed`. The fixed-twist isomorphism is built
on the actual extended module, and its conjugation on Hom spaces agrees
with the canonical coefficient Galois action. Twisted indecomposable
summands therefore remain summands of the same extended base module.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- The coefficient automorphism is semilinear for the actual K-algebra. -/
theorem scalarExtensionAlgebraAut_semilinear (σ : K ≃ₐ[k] K) :
    IsSemilinearAlgebraAut σ.toRingEquiv
      (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv := by
  intro c
  change scalarExtensionAlgebraAut σ (c ⊗ₜ[k] (1 : A)) = σ c ⊗ₜ[k] (1 : A)
  exact scalarExtensionAlgebraAut_tmul σ c 1

/-- The coefficient action of σ identifies the σ-twist with the original
extended module. Its inverse is the manuscript's map t_(σ,X). -/
def scalarExtensionTwistIso (σ : K ≃ₐ[k] K) (M : ModuleCat.{max u v} A) :
    (moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv).obj
      (scalarExtensionObject (k := k) (K := K) M) ≅
        scalarExtensionObject (k := k) (K := K) M := by
  let α := scalarExtensionAlgebraAut (A := A) σ
  let e :
      (moduleTwist α.toRingEquiv).obj
        (scalarExtensionObject (k := k) (K := K) M) ≃ₗ[K ⊗[k] A]
          scalarExtensionObject (k := k) (K := K) M := {
    toAddEquiv := (tensorGaloisAction (V := M) σ).toAddEquiv
    map_smul' := fun a x => by
      change tensorGaloisAction σ
          (scalarExtensionRepresentation (k := k) M (α.symm a) x) =
        scalarExtensionRepresentation (k := k) M a (tensorGaloisAction σ x)
      rw [tensorGaloisAction_representation]
      change scalarExtensionRepresentation (k := k) M
        (α (α.symm a)) (tensorGaloisAction σ x) = _
      rw [α.apply_symm_apply]
  }
  exact e.toModuleIso

@[simp]
theorem scalarExtensionTwistIso_hom_tmul (σ : K ≃ₐ[k] K)
    (M : ModuleCat.{max u v} A) (c : K) (x : M) :
    (scalarExtensionTwistIso σ M).hom (c ⊗ₜ[k] x) = σ c ⊗ₜ[k] x :=
  tensorGaloisAction_tmul σ c x

@[simp]
theorem scalarExtensionTwistIso_inv_tmul (σ : K ≃ₐ[k] K)
    (M : ModuleCat.{max u v} A) (c : K) (x : M) :
    (scalarExtensionTwistIso σ M).inv (c ⊗ₜ[k] x) = σ.symm c ⊗ₜ[k] x := by
  apply (ModuleCat.mono_iff_injective _).mp
    (inferInstance : Mono (scalarExtensionTwistIso σ M).hom)
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    scalarExtensionTwistIso_hom_tmul, σ.apply_symm_apply]

/-- Fixed-twist conjugation on actual extended module maps. -/
def scalarExtensionTwistConjugate (σ : K ≃ₐ[k] K)
    {M N : ModuleCat.{max u v} A}
    (f : scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) :
    scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N :=
  (scalarExtensionTwistIso σ M).inv ≫
    (moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv).map f ≫
      (scalarExtensionTwistIso σ N).hom

variable [Module.Finite k A]

/-- Conjugating a pure tensor map changes only its scalar coefficient. -/
theorem scalarExtensionTwistConjugate_tmul (σ : K ≃ₐ[k] K)
    (M N : ModuleCat.{max u v} A) [Module.Finite k M]
    (c : K) (f : M ⟶ N) :
    scalarExtensionTwistConjugate σ
        (moduleHomScalarExtensionEquiv M N (c ⊗ₜ[k] f)) =
      moduleHomScalarExtensionEquiv M N (σ c ⊗ₜ[k] f) := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul d x =>
    simp only [scalarExtensionTwistConjugate, ModuleCat.comp_apply,
      scalarExtensionTwistIso_inv_tmul, moduleTwist_map_apply,
      moduleHomScalarExtensionEquiv_tmul_apply, scalarExtensionTwistIso_hom_tmul,
      map_mul, σ.apply_symm_apply]
  | add z z' hz hz' =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hz'

/-- The canonical Hom equivalence is equivariant for the actual twist,
including arbitrary sums of tensor maps. -/
theorem scalarExtensionTwistConjugate_homEquiv (σ : K ≃ₐ[k] K)
    (M N : ModuleCat.{max u v} A) [Module.Finite k M]
    (z : K ⊗[k] (M ⟶ N)) :
    scalarExtensionTwistConjugate σ (moduleHomScalarExtensionEquiv M N z) =
      moduleHomScalarExtensionEquiv M N (tensorGaloisAction σ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c f =>
    rw [tensorGaloisAction_tmul]
    exact scalarExtensionTwistConjugate_tmul σ M N c f
  | add z z' hz hz' =>
    simpa only [map_add, scalarExtensionTwistConjugate, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp] using congrArg₂ (· + ·) hz hz'

omit [Module.Finite k A] in
/-- Twisting preserves the summand relation inside this fixed extended
module. No algebraic-closure or transitivity premise is needed. -/
theorem isIndecomposableSummand_scalarExtension_twist
    (σ : K ≃ₐ[k] K) (M : FiniteModule k A)
    (U : IndecomposableModule K (K ⊗[k] A))
    (hU : IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) M)) :
    IsIndecomposableSummand
      (twistIndecomposableModule (scalarExtensionAlgebraAut_semilinear σ) U)
        (scalarExtensionFiniteModule (L := K) M) := by
  obtain ⟨i, p, hip⟩ := hU
  let F := moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv
  let e := scalarExtensionTwistIso σ M.val
  refine ⟨F.map i ≫ e.hom, e.inv ≫ F.map p, ?_⟩
  change (F.map i ≫ e.hom) ≫ (e.inv ≫ F.map p) = 𝟙 (F.obj U.obj)
  rw [Category.assoc, ← Category.assoc e.hom e.inv, e.hom_inv_id,
    Category.id_comp, ← F.map_comp, hip, F.map_id]

end

end C3PerfectField
