-- Ported for the pinned Lean/Mathlib version with Doubao assistance; original notices retained.
module

public import C3PerfectField.ScalarExtensionModules
public import C3PerfectField.EndCompatibility
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
Manuscript `lem:hom-base`: the canonical Hom scalar-extension map,
on the actual modules and morphisms of `scalarExtensionFunctor`.
The A-linearity equations form the kernel of a linear map.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v w t s

section VectorSpaces

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  {U : Type w} {V : Type t} [AddCommGroup U] [AddCommGroup V]
  [Module k U] [Module k V] [Module.Finite k U]

/-- The canonical vector-space Hom scalar-extension equivalence. -/
def vectorHomScalarExtensionEquiv :
    (K ⊗[k] (U →ₗ[k] V)) ≃ₗ[K] ((K ⊗[k] U) →ₗ[K] (K ⊗[k] V)) := by
  let : Module.FinitePresentation k U := Module.finitePresentation_of_finite k U
  exact (Module.FinitePresentation.isBaseChange_map k U V K).equiv

@[simp]
theorem vectorHomScalarExtensionEquiv_tmul (c : K) (f : U →ₗ[k] V) :
    vectorHomScalarExtensionEquiv (c ⊗ₜ[k] f) = c • f.baseChange K :=
  rfl

@[simp]
theorem vectorHomScalarExtensionEquiv_tmul_apply (c d : K) (f : U →ₗ[k] V) (x : U) :
    vectorHomScalarExtensionEquiv (c ⊗ₜ[k] f) (d ⊗ₜ[k] x) =
      (c * d) ⊗ₜ[k] f x := by
  simp only [vectorHomScalarExtensionEquiv_tmul, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

end VectorSpaces

section Equations

variable {F : Type u} {B : Type v} {U : Type w} {V : Type t}
  [Field F] [Ring B] [Algebra F B]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]

/-- The linear system f R_b - S_b f, before and after scalar extension. -/
def representationHomDefect
    (ρ : B →ₐ[F] Module.End F U) (τ : B →ₐ[F] Module.End F V) :
    (U →ₗ[F] V) →ₗ[F] (B →ₗ[F] (U →ₗ[F] V)) where
  toFun f := {
    toFun := fun b => f.comp (ρ b) - (τ b).comp f
    map_add' := fun b b' => by ext x; simp; abel
    map_smul' := fun c b => by ext x; simp [smul_sub]
  }
  map_add' f g := by ext b x; simp; abel
  map_smul' c f := by ext b x; simp [smul_sub]

@[simp]
theorem representationHomDefect_apply
    (ρ : B →ₐ[F] Module.End F U) (τ : B →ₐ[F] Module.End F V)
    (f : U →ₗ[F] V) (b : B) (x : U) :
    representationHomDefect ρ τ f b x = f (ρ b x) - τ b (f x) := rfl

theorem mem_representationHomDefect_ker
    (ρ : B →ₐ[F] Module.End F U) (τ : B →ₐ[F] Module.End F V)
    (f : U →ₗ[F] V) :
    f ∈ (representationHomDefect ρ τ).ker ↔
      ∀ b x, f (ρ b x) = τ b (f x) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h b x
    exact sub_eq_zero.mp (congrArg (fun q => q b x) h)
  · intro h
    ext b x
    exact sub_eq_zero.mpr (h b x)

end Equations

variable {k : Type u} {K : Type w} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- The actual A-linearity equations over k. -/
def moduleHomDefect (M N : ModuleCat.{max u v} A) :
    (M →ₗ[k] N) →ₗ[k] (A →ₗ[k] (M →ₗ[k] N)) :=
  representationHomDefect (Algebra.lsmul k k M) (Algebra.lsmul k k N)

/-- Module-category Hom is the kernel of the action equations. -/
def moduleHomKernelEquiv (M N : ModuleCat.{max u v} A) :
    (M ⟶ N) ≃ₗ[k] (moduleHomDefect (k := k) M N).ker where
  toFun f := ⟨f.hom.restrictScalars k,
    (mem_representationHomDefect_ker _ _ _).mpr (fun a x => f.hom.map_smul a x)⟩
  invFun f := ModuleCat.ofHom {
    toAddHom := f.val.toAddHom
    map_smul' := (mem_representationHomDefect_ker _ _ _).mp f.property
  }
  left_inv _f := rfl
  right_inv _f := rfl
  map_add' _f _g := rfl
  map_smul' _c _f := rfl

@[simp]
theorem moduleHomKernelEquiv_apply (M N : ModuleCat.{max u v} A) (f : M ⟶ N) :
    (moduleHomKernelEquiv (k := k) M N f).val = f.hom.restrictScalars k := rfl

/-- The action equations on the native tensor vector spaces over K. -/
def scalarExtendedHomDefect (M N : ModuleCat.{max u v} A) :
    ((K ⊗[k] M) →ₗ[K] (K ⊗[k] N)) →ₗ[K]
      ((K ⊗[k] A) →ₗ[K] ((K ⊗[k] M) →ₗ[K] (K ⊗[k] N))) :=
  representationHomDefect
    (scalarExtensionRepresentation (k := k) (K := K) M)
    (scalarExtensionRepresentation (k := k) (K := K) N)

/-- Forget A_K-linearity, using the checked native K-scalar equivalences. -/
def scalarExtendedHomUnderlying (M N : ModuleCat.{max u v} A) :
    (scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) →ₗ[K]
        ((K ⊗[k] M) →ₗ[K] (K ⊗[k] N)) where
  toFun f :=
    (scalarExtensionObjectScalarEquiv (k := k) (K := K) N).toLinearMap ∘ₗ
      f.hom.restrictScalars K ∘ₗ
        (scalarExtensionObjectScalarEquiv (k := k) (K := K) M).symm.toLinearMap
  map_add' f g := by ext z; rfl
  map_smul' c f := by
    ext z
    exact (scalarExtensionObjectScalarEquiv (k := k) (K := K) N).map_smul c _

@[simp]
theorem scalarExtendedHomUnderlying_apply (M N : ModuleCat.{max u v} A)
    (f : scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) (z : K ⊗[k] M) :
    scalarExtendedHomUnderlying M N f z = f z := rfl

/-- The actual extended-module Hom is the kernel over K. -/
def scalarExtendedHomKernelEquiv (M N : ModuleCat.{max u v} A) :
    (scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) ≃ₗ[K]
        (scalarExtendedHomDefect (k := k) (K := K) M N).ker where
  toFun f := ⟨scalarExtendedHomUnderlying M N f,
    (mem_representationHomDefect_ker _ _ _).mpr (fun a x => f.hom.map_smul a x)⟩
  invFun f := by
    letI := Module.compHom (K ⊗[k] M)
      (scalarExtensionRepresentation (k := k) (K := K) M).toRingHom
    letI := Module.compHom (K ⊗[k] N)
      (scalarExtensionRepresentation (k := k) (K := K) N).toRingHom
    exact ModuleCat.ofHom {
      toAddHom := f.val.toAddHom
      map_smul' := (mem_representationHomDefect_ker _ _ _).mp f.property
    }
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := Subtype.ext ((scalarExtendedHomUnderlying M N).map_add f g)
  map_smul' c f := Subtype.ext ((scalarExtendedHomUnderlying M N).map_smul c f)

variable [Module.Finite k A]

/-- Scalar extension of the space in which the A-linearity equations take
their values. Both Hom equivalences are the canonical ones. -/
def homDefectScalarExtensionEquiv (M N : ModuleCat.{max u v} A) [Module.Finite k M] :
    (K ⊗[k] (A →ₗ[k] (M →ₗ[k] N))) ≃ₗ[K]
      ((K ⊗[k] A) →ₗ[K] ((K ⊗[k] M) →ₗ[K] (K ⊗[k] N))) :=
  (vectorHomScalarExtensionEquiv (k := k) (K := K) (U := A)).trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl K (K ⊗[k] A))
      (vectorHomScalarExtensionEquiv (k := k) (K := K) (U := M)))

/-- The original equations extend to exactly the actual A_K-linearity
equations, as a commuting square of K-linear maps. -/
theorem homDefect_scalarExtension (M N : ModuleCat.{max u v} A) [Module.Finite k M] :
    (homDefectScalarExtensionEquiv (k := k) (K := K) M N).toLinearMap ∘ₗ
        (moduleHomDefect (k := k) M N).baseChange K =
      (scalarExtendedHomDefect (k := k) (K := K) M N) ∘ₗ
        (vectorHomScalarExtensionEquiv (k := k) (K := K) (U := M) (V := N)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c f
  apply TensorProduct.AlgebraTensorModule.ext
  intro d a
  apply TensorProduct.AlgebraTensorModule.ext
  intro e x
  simp [homDefectScalarExtensionEquiv, moduleHomDefect, scalarExtendedHomDefect,
    scalarExtensionRepresentation_tmul, TensorProduct.tmul_sub, smul_sub,
    TensorProduct.smul_tmul', smul_eq_mul]

/-- Exactness of tensor products restricts the commuting square to an
equivalence between the actual kernels. -/
def homKernelScalarExtensionEquiv (M N : ModuleCat.{max u v} A) [Module.Finite k M] :
    (K ⊗[k] (moduleHomDefect (k := k) M N).ker) ≃ₗ[K]
      (scalarExtendedHomDefect (k := k) (K := K) M N).ker := by
  let D := moduleHomDefect (k := k) M N
  let D' := scalarExtendedHomDefect (k := k) (K := K) M N
  let e := vectorHomScalarExtensionEquiv (k := k) (K := K) (U := M) (V := N)
  let q := homDefectScalarExtensionEquiv (k := k) (K := K) M N
  have hcomm : q.toLinearMap ∘ₗ D.baseChange K = D' ∘ₗ e.toLinearMap :=
    homDefect_scalarExtension M N
  let j := D.ker.subtype.baseChange K
  have hj : ∀ z, e (j z) ∈ D'.ker := by
    intro z
    rw [LinearMap.mem_ker]
    change (D' ∘ₗ e.toLinearMap) (j z) = 0
    rw [← hcomm]
    have hz : (D.baseChange K) (j z) = 0 :=
      (scalarExtension_exact (k := k) (K := K) D.exact_subtype_ker_map).apply_apply_eq_zero z
    change q ((D.baseChange K) (j z)) = 0
    rw [hz, map_zero]
  let f : (K ⊗[k] D.ker) →ₗ[K] D'.ker :=
    (e.toLinearMap ∘ₗ j).codRestrict D'.ker hj
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' := congrArg (fun z : D'.ker => z.val) hxy
    change e (j x) = e (j y) at hxy'
    exact scalarExtension_injective D.ker.subtype D.ker.subtype_injective
      (e.injective hxy')
  · intro g
    have hg : D.baseChange K (e.symm g.val) = 0 := by
      apply q.injective
      change (q.toLinearMap ∘ₗ D.baseChange K) (e.symm g.val) = q 0
      rw [hcomm]
      change D' (e (e.symm g.val)) = q 0
      rw [e.apply_symm_apply, map_zero]
      exact g.property
    have hz : e.symm g.val ∈ LinearMap.range j := by
      change e.symm g.val ∈ D.ker.baseChange K
      rw [← scalarExtension_ker]
      exact hg
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, Subtype.ext ?_⟩
    change e (j z) = g.val
    rw [hz, e.apply_symm_apply]

/-- The kernel equivalence uses the canonical tensor map on pure tensors. -/
theorem homKernelScalarExtensionEquiv_tmul (M N : ModuleCat.{max u v} A)
    [Module.Finite k M] (c : K) (f : (moduleHomDefect (k := k) M N).ker) :
    (homKernelScalarExtensionEquiv (k := k) (K := K) M N (c ⊗ₜ[k] f)).val =
      c • f.val.baseChange K := by
  change vectorHomScalarExtensionEquiv
    ((moduleHomDefect (k := k) M N).ker.subtype.baseChange K (c ⊗ₜ[k] f)) = _
  rw [LinearMap.baseChange_tmul, vectorHomScalarExtensionEquiv_tmul]
  rfl

/-- Manuscript `lem:hom-base`, for every field extension, on the actual
module-category Hom spaces. No perfection or algebraic closure is assumed. -/
def moduleHomScalarExtensionEquiv (M N : ModuleCat.{max u v} A) [Module.Finite k M] :
    (K ⊗[k] (M ⟶ N)) ≃ₗ[K]
      (scalarExtensionObject (k := k) (K := K) M ⟶
        scalarExtensionObject (k := k) (K := K) N) :=
  ((moduleHomKernelEquiv (k := k) M N).baseChange k K).trans
    ((homKernelScalarExtensionEquiv (k := k) (K := K) M N).trans
      (scalarExtendedHomKernelEquiv (k := k) (K := K) M N).symm)

@[simp]
theorem moduleHomScalarExtensionEquiv_tmul (M N : ModuleCat.{max u v} A)
    [Module.Finite k M] (c : K) (f : M ⟶ N) :
    moduleHomScalarExtensionEquiv (k := k) (K := K) M N (c ⊗ₜ[k] f) =
      c • scalarExtensionMap (k := k) (K := K) f := by
  apply (scalarExtendedHomKernelEquiv (k := k) (K := K) M N).injective
  apply Subtype.ext
  change (homKernelScalarExtensionEquiv (k := k) (K := K) M N
    (((moduleHomKernelEquiv (k := k) M N).baseChange k K) (c ⊗ₜ[k] f))).val = _
  rw [LinearEquiv.baseChange_tmul, homKernelScalarExtensionEquiv_tmul]
  apply LinearMap.ext
  intro z
  change (c • (f.hom.restrictScalars k).baseChange K) z =
    scalarExtendedHomUnderlying M N (c • scalarExtensionMap (k := k) (K := K) f) z
  rw [map_smul]
  rfl

@[simp]
theorem moduleHomScalarExtensionEquiv_tmul_apply (M N : ModuleCat.{max u v} A)
    [Module.Finite k M] (c d : K) (f : M ⟶ N) (x : M) :
    moduleHomScalarExtensionEquiv (k := k) (K := K) M N (c ⊗ₜ[k] f) (d ⊗ₜ[k] x) =
      (c * d) ⊗ₜ[k] f x := by
  rw [moduleHomScalarExtensionEquiv_tmul]
  change scalarExtensionObjectScalarEquiv (k := k) (K := K) N
    (c • scalarExtensionMap (k := k) (K := K) f (d ⊗ₜ[k] x)) = _
  rw [map_smul, scalarExtensionMap_tmul]
  exact TensorProduct.smul_tmul' c d (f x)

/-- Tensor extension of the original bilinear composition map. -/
def moduleHomTensorComposition (M N P : ModuleCat.{max u v} A) :
    ((K ⊗[k] (M ⟶ N)) ⊗[K] (K ⊗[k] (N ⟶ P))) →ₗ[K] (K ⊗[k] (M ⟶ P)) :=
  (TensorProduct.lift (Linear.comp (S := k) M N P)).baseChange K ∘ₗ
    (TensorProduct.AlgebraTensorModule.congr (TensorProduct.lid K K)
      (LinearEquiv.refl k ((M ⟶ N) ⊗[k] (N ⟶ P)))).toLinearMap ∘ₗ
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
      k k K K K (M ⟶ N) K (N ⟶ P)).toLinearMap

omit [Module.Finite k A] in
@[simp]
theorem moduleHomTensorComposition_tmul (M N P : ModuleCat.{max u v} A)
    (c d : K) (f : M ⟶ N) (g : N ⟶ P) :
    moduleHomTensorComposition M N P ((c ⊗ₜ[k] f) ⊗ₜ[K] (d ⊗ₜ[k] g)) =
      (c * d) ⊗ₜ[k] (f ≫ g) := by
  simp [moduleHomTensorComposition]

/-- The manuscript Hom equivalences respect composition on all tensors. -/
theorem moduleHomScalarExtensionEquiv_comp (M N P : ModuleCat.{max u v} A)
    [Module.Finite k M] [Module.Finite k N]
    (f : K ⊗[k] (M ⟶ N)) (g : K ⊗[k] (N ⟶ P)) :
    moduleHomScalarExtensionEquiv M P
        (moduleHomTensorComposition M N P (f ⊗ₜ[K] g)) =
      moduleHomScalarExtensionEquiv M N f ≫ moduleHomScalarExtensionEquiv N P g := by
  induction f using TensorProduct.inductionOn with
  | tmul c f =>
    induction g using TensorProduct.inductionOn with
    | tmul d g =>
      simp only [moduleHomTensorComposition_tmul, moduleHomScalarExtensionEquiv_tmul,
        Linear.smul_comp, Linear.comp_smul, smul_smul]
      rw [mul_comm d c]
      congr 1
      exact (scalarExtensionFunctor (k := k) (K := K) (A := A)).map_comp f g
    | add g g' hg hg' =>
      simp only [TensorProduct.tmul_add, map_add, hg, hg', Preadditive.comp_add]
  | add f f' hf hf' =>
    simp only [TensorProduct.add_tmul, map_add, hf, hf', Preadditive.add_comp]

/-- In particular, the identity is preserved by the canonical inclusion. -/
@[simp]
theorem moduleHomScalarExtensionEquiv_id (M : ModuleCat.{max u v} A) [Module.Finite k M] :
    moduleHomScalarExtensionEquiv (k := k) (K := K) M M (1 ⊗ₜ[k] 𝟙 M) =
      𝟙 (scalarExtensionObject (k := k) (K := K) M) := by
  rw [moduleHomScalarExtensionEquiv_tmul, one_smul]
  exact (scalarExtensionFunctor (k := k) (K := K) (A := A)).map_id M

/-- The endomorphism case is an algebra equivalence, with the usual
endomorphism multiplication order. -/
def moduleEndScalarExtensionAlgEquiv (M : ModuleCat.{max u v} A) [Module.Finite k M] :
    (K ⊗[k] End M) ≃ₐ[K] End (scalarExtensionObject (k := k) (K := K) M) := by
  let e : (K ⊗[k] End M) ≃ₗ[K]
      End (scalarExtensionObject (k := k) (K := K) M) :=
    ((End.linearEquiv (R := k) (X := M)).baseChange k K).trans
      ((moduleHomScalarExtensionEquiv (k := k) (K := K) M M).trans
        (End.linearEquiv (R := K)).symm)
  refine AlgEquiv.ofLinearEquiv e ?_ ?_
  · change e (1 ⊗ₜ[k] (1 : End M)) = 1
    apply End.homEquiv.injective
    exact moduleHomScalarExtensionEquiv_id M
  · intro f g
    induction f using TensorProduct.inductionOn with
    | tmul c f =>
      induction g using TensorProduct.inductionOn with
      | tmul d g =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        apply End.homEquiv.injective
        simp only [e, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
        change moduleHomScalarExtensionEquiv M M
          ((c * d) ⊗ₜ[k] (g.asHom ≫ f.asHom)) =
            moduleHomScalarExtensionEquiv M M (d ⊗ₜ[k] g.asHom) ≫
              moduleHomScalarExtensionEquiv M M (c ⊗ₜ[k] f.asHom)
        rw [mul_comm c d, ← moduleHomTensorComposition_tmul]
        exact moduleHomScalarExtensionEquiv_comp M M M _ _
      | add g g' hg hg' => simp only [mul_add, map_add, hg, hg']
    | add f f' hf hf' => simp only [add_mul, map_add, hf, hf']

@[simp]
theorem moduleEndScalarExtensionAlgEquiv_tmul (M : ModuleCat.{max u v} A)
    [Module.Finite k M] (c : K) (f : End M) :
    moduleEndScalarExtensionAlgEquiv (k := k) (K := K) M (c ⊗ₜ[k] f) =
      c • End.of (scalarExtensionMap (k := k) (K := K) f.asHom) := by
  apply End.homEquiv.injective
  exact moduleHomScalarExtensionEquiv_tmul M M c f.asHom

/-- Scalar extension preserves the dimension of the actual module Hom space. -/
theorem finrank_scalarExtension_hom (M N : ModuleCat.{max u v} A) [Module.Finite k M] :
    Module.finrank K (scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N) = Module.finrank k (M ⟶ N) :=
  (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).symm.finrank_eq.trans
    finrank_scalarExtension

end

end C3PerfectField
