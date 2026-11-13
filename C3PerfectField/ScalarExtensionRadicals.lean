module

public import C3PerfectField.ScalarExtensionHom
public import C3PerfectField.ScalarExtensionIdeals
public import C3PerfectField.RadicalBlocks
public import C3PerfectField.HomDimensions

/-!
Manuscript `lem:radical-base`, on the actual scalar-extension functor.
The categorical radical is the inverse image of the Jacobson radical
under an off-diagonal corner map. Flatness commutes with that inverse
image, and the canonical Hom and End equivalences commute with the corner.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct

universe u v w

variable {k : Type u} {K : Type w} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- The off-diagonal corner as a linear map into the endomorphism algebra. -/
def radicalCorner (M N : ModuleCat.{max u v} A) :
    (M ⟶ N) →ₗ[k] End (M ⊞ N) :=
  (End.linearEquiv (R := k)).symm.toLinearMap ∘ₗ
    Linear.rightComp k (M ⊞ N) biprod.inr ∘ₗ
      Linear.leftComp k N biprod.fst

@[simp]
theorem radicalCorner_apply (M N : ModuleCat.{max u v} A) (f : M ⟶ N) :
    radicalCorner (k := k) M N f =
      End.of (biprod.fst ≫ f ≫ biprod.inr : M ⊞ N ⟶ M ⊞ N) := rfl

theorem radicalSubmodule_eq_comap_corner (M N : ModuleCat.{max u v} A) :
    radicalSubmodule (k := k) M N =
      ((Ideal.jacobson (⊥ : Ideal (End (M ⊞ N)))).restrictScalars k).comap
        (radicalCorner M N) := by
  ext f
  exact isRadical_iff_corner_mem_jacobson f

/-- The same corner in F(M ⊞ N), using the actual images of its splitting maps. -/
def scalarExtendedRadicalCorner (M N : ModuleCat.{max u v} A) :
    (scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) →ₗ[K]
        End (scalarExtensionObject (k := k) (K := K) (M ⊞ N)) :=
  (End.linearEquiv (R := K)).symm.toLinearMap ∘ₗ
    Linear.rightComp K _ (scalarExtensionMap (k := k) (K := K) biprod.inr) ∘ₗ
      Linear.leftComp K _ (scalarExtensionMap (k := k) (K := K) biprod.fst)

@[simp]
theorem scalarExtendedRadicalCorner_apply (M N : ModuleCat.{max u v} A)
    (f : scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) :
    scalarExtendedRadicalCorner (k := k) (K := K) M N f =
      End.of (scalarExtensionMap (k := k) (K := K) biprod.fst ≫ f ≫
        scalarExtensionMap (k := k) (K := K) biprod.inr) := rfl

/-- Only the splitting equations are needed to recover the extended radical. -/
theorem isRadical_iff_scalarExtendedCorner_mem_jacobson
    (M N : ModuleCat.{max u v} A)
    (f : scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) :
    IsRadical.{u, max v w} (K ⊗[k] A) f ↔
      scalarExtendedRadicalCorner (k := k) (K := K) M N f ∈
        Ideal.jacobson (⊥ : Ideal
          (End (scalarExtensionObject (k := k) (K := K) (M ⊞ N)))) := by
  rw [scalarExtendedRadicalCorner_apply,
    ← isRadical_end_iff_mem_jacobson.{u, max v w}]
  constructor
  · intro hf
    exact (hf.postcomp _).precomp _
  · intro hf
    have h := (hf.precomp (scalarExtensionMap (k := k) (K := K) biprod.inl)).postcomp
      (scalarExtensionMap (k := k) (K := K) biprod.snd)
    let F := scalarExtensionFunctor (k := k) (K := K) (A := A)
    change IsRadical.{u, max v w} (K ⊗[k] A)
      (F.map biprod.inl ≫ (F.map biprod.fst ≫ f ≫ F.map biprod.inr) ≫
        F.map biprod.snd) at h
    have hl : F.map (biprod.inl : M ⟶ M ⊞ N) ≫ F.map biprod.fst = 𝟙 (F.obj M) := by
      rw [← F.map_comp, biprod.inl_fst, F.map_id]
    have hr : F.map (biprod.inr : N ⟶ M ⊞ N) ≫ F.map biprod.snd = 𝟙 (F.obj N) := by
      rw [← F.map_comp, biprod.inr_snd, F.map_id]
    have heq : F.map (biprod.inl : M ⟶ M ⊞ N) ≫
        (F.map biprod.fst ≫ f ≫ F.map (biprod.inr : N ⟶ M ⊞ N)) ≫
        F.map biprod.snd = f := by
      calc
        _ = (F.map (biprod.inl : M ⟶ M ⊞ N) ≫ F.map biprod.fst) ≫ f ≫
            (F.map (biprod.inr : N ⟶ M ⊞ N) ≫ F.map biprod.snd) := by
              simp only [Category.assoc]
        _ = f := by
          rw [hl, hr, Category.id_comp]
          change f ≫ 𝟙 (scalarExtensionObject (k := k) (K := K) N) = f
          exact Category.comp_id f
    simpa only [heq] using h

/-- Binary direct sums of finite modules are finite over the same field. -/
theorem finite_biprod_module (M N : ModuleCat.{max u v} A)
    [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (M ⊞ N : ModuleCat.{max u v} A) := by
  let e := (ModuleCat.biprodIsoProd M N).toLinearEquiv.restrictScalars k
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- The actual endomorphism algebra of a finite module is finite over k. -/
theorem finite_module_end (M : ModuleCat.{max u v} A) [Module.Finite k M] :
    Module.Finite k (End M) := by
  let : Module.Finite k (M ⟶ M) :=
    finite_module_hom (⟨M, inferInstance⟩ : FiniteModule k A) ⟨M, inferInstance⟩
  exact FiniteDimensional.of_injective (End.linearEquiv (R := k)).toLinearMap
    (End.linearEquiv (R := k)).injective

variable [Module.Finite k A]

/-- The corner square commutes on all tensors with the canonical Hom/End maps. -/
theorem radicalCorner_scalarExtension (M N : ModuleCat.{max u v} A)
    [Module.Finite k M] [Module.Finite k N] :
    letI := finite_biprod_module (k := k) M N
    (scalarExtendedRadicalCorner (k := k) (K := K) M N) ∘ₗ
        (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).toLinearMap =
      (moduleEndScalarExtensionAlgEquiv (k := k) (K := K) (M ⊞ N)).toLinearMap ∘ₗ
        (radicalCorner (k := k) M N).baseChange K := by
  let := finite_biprod_module (k := k) M N
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c f =>
    change scalarExtendedRadicalCorner (k := k) (K := K) M N
      (moduleHomScalarExtensionEquiv (k := k) (K := K) M N (c ⊗ₜ[k] f)) =
        moduleEndScalarExtensionAlgEquiv (k := k) (K := K) (M ⊞ N)
          ((radicalCorner (k := k) M N).baseChange K (c ⊗ₜ[k] f))
    rw [moduleHomScalarExtensionEquiv_tmul, map_smul, LinearMap.baseChange_tmul,
      moduleEndScalarExtensionAlgEquiv_tmul, radicalCorner_apply,
      scalarExtendedRadicalCorner_apply]
    congr 1
    apply End.homEquiv.injective
    let F := scalarExtensionFunctor (k := k) (K := K) (A := A)
    change F.map (biprod.fst : M ⊞ N ⟶ M) ≫ F.map f ≫ F.map biprod.inr =
      F.map (biprod.fst ≫ f ≫ biprod.inr)
    rw [F.map_comp, F.map_comp]
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The canonical Hom map identifies categorical radical subspaces
under the manuscript's literal fixed-field hypothesis. -/
theorem radicalSubmodule_scalarExtension_of_fixedField
    (G : Subgroup (K ≃ₐ[k] K)) (hG : IntermediateField.fixedField G = ⊥)
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N] :
    (categoricalRadicalSubmodule.{w, max v w, u} (k := K)
      (scalarExtensionObject (k := k) (K := K) M)
      (scalarExtensionObject (k := k) (K := K) N)).comap
        (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).toLinearMap =
      (radicalSubmodule (k := k) M N).baseChange K := by
  let := finite_biprod_module (k := k) M N
  let := finite_module_end (k := k) (M ⊞ N)
  let C := radicalCorner (k := k) M N
  let C' := scalarExtendedRadicalCorner (k := k) (K := K) M N
  let e := moduleHomScalarExtensionEquiv (k := k) (K := K) M N
  let d := moduleEndScalarExtensionAlgEquiv (k := k) (K := K) (M ⊞ N)
  have hcomm : C' ∘ₗ e.toLinearMap = d.toLinearMap ∘ₗ C.baseChange K :=
    radicalCorner_scalarExtension M N
  have hJ := jacobson_scalarExtension_of_fixedField (A := End (M ⊞ N)) G hG
  ext z
  change IsRadical.{u, max v w} (K ⊗[k] A) (e z) ↔
    z ∈ (radicalSubmodule (k := k) M N).baseChange K
  rw [isRadical_iff_scalarExtendedCorner_mem_jacobson]
  change C' (e z) ∈ Ideal.jacobson (⊥ : Ideal
    (End (scalarExtensionObject (k := k) (K := K) (M ⊞ N)))) ↔ _
  have hc : C' (e z) = d (C.baseChange K z) := LinearMap.congr_fun hcomm z
  rw [hc]
  have hd : d (C.baseChange K z) ∈ Ideal.jacobson (⊥ : Ideal
      (End (scalarExtensionObject (k := k) (K := K) (M ⊞ N)))) ↔
      C.baseChange K z ∈ Ideal.jacobson (⊥ : Ideal (K ⊗[k] End (M ⊞ N))) :=
    ringEquiv_mem_jacobson_iff d.toRingEquiv _
  rw [hd, hJ]
  change C.baseChange K z ∈
    ((Ideal.jacobson (⊥ : Ideal (End (M ⊞ N)))).restrictScalars k).baseChange K ↔ _
  rw [radicalSubmodule_eq_comap_corner, scalarExtension_comap]
  rfl

/-- Manuscript `lem:radical-base`: perfection supplies the fixed field,
and no further premise is placed on the modules or extension. -/
theorem algebraicClosure_radicalSubmodule_scalarExtension
    [PerfectField k] [IsAlgClosure k K]
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N] :
    (categoricalRadicalSubmodule.{w, max v w, u} (k := K)
      (scalarExtensionObject (k := k) (K := K) M)
      (scalarExtensionObject (k := k) (K := K) N)).comap
        (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).toLinearMap =
      (radicalSubmodule (k := k) M N).baseChange K :=
  radicalSubmodule_scalarExtension_of_fixedField _ algebraicClosure_fixedField M N

/-- Elementwise form of the actual radical equality. -/
theorem isRadical_moduleHomScalarExtensionEquiv_iff
    [PerfectField k] [IsAlgClosure k K]
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N]
    (z : K ⊗[k] (M ⟶ N)) :
    IsRadical.{u, max v w} (K ⊗[k] A)
      (moduleHomScalarExtensionEquiv (k := k) (K := K) M N z) ↔
        z ∈ (radicalSubmodule (k := k) M N).baseChange K := by
  exact SetLike.ext_iff.mp (algebraicClosure_radicalSubmodule_scalarExtension M N) z

/-- The displayed subspace equality inside the identified Hom space. -/
theorem algebraicClosure_radicalSubmodule_scalarExtension_map
    [PerfectField k] [IsAlgClosure k K]
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N] :
    ((radicalSubmodule (k := k) M N).baseChange K).map
      (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).toLinearMap =
        categoricalRadicalSubmodule.{w, max v w, u} (k := K)
          (scalarExtensionObject (k := k) (K := K) M)
          (scalarExtensionObject (k := k) (K := K) N) := by
  rw [← algebraicClosure_radicalSubmodule_scalarExtension M N]
  exact Submodule.map_comap_eq_of_surjective
    (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).surjective _

end

end C3PerfectField
