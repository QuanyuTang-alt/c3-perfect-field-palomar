module

public import C3PerfectField.GaloisSubspaceDescent
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic

/-!
The actual scalar extension K ⊗[k] V and its coefficient Galois action.
This proves both assertions of manuscript `lem:subspace-descent` on tensor
spaces, using the canonical inclusion of the descended subspace.
-/

@[expose] public section

namespace C3PerfectField

noncomputable section

open Module
open scoped TensorProduct

universe u v w t

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  {V : Type w} [AddCommGroup V] [Module k V]

/-- Manuscript `def:scalar`: apply σ only to the scalar tensor factor. -/
def tensorGaloisAction (σ : K ≃ₐ[k] K) :
    (K ⊗[k] V) ≃ₗ[k] (K ⊗[k] V) :=
  σ.toLinearEquiv.rTensor V

@[simp]
theorem tensorGaloisAction_tmul (σ : K ≃ₐ[k] K) (c : K) (x : V) :
    tensorGaloisAction σ (c ⊗ₜ[k] x) = σ c ⊗ₜ[k] x :=
  TensorProduct.congr_tmul _ _ _ _

@[simp]
theorem tensorGaloisAction_one_tmul (σ : K ≃ₐ[k] K) (x : V) :
    tensorGaloisAction σ (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x := by
  simp only [tensorGaloisAction_tmul, map_one]

/-- The standard scalar-extension inclusion is injective. -/
theorem scalarTensorInclusion_injective :
    Function.Injective (TensorProduct.mk k K V 1) :=
  Module.Flat.tensorProduct_mk_injective k V K

/-- The coefficient action is semilinear over K, rather than K-linear. -/
theorem tensorGaloisAction_smul (σ : K ≃ₐ[k] K) (c : K) (z : K ⊗[k] V) :
    tensorGaloisAction σ (c • z) = σ c • tensorGaloisAction σ z := by
  induction z using TensorProduct.inductionOn with
  | tmul d x =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, tensorGaloisAction_tmul, map_mul]
  | add z z' hz hz' =>
    simp only [smul_add, map_add, hz, hz']

/-- Every scalar-extended subspace is invariant under base-field
automorphisms of the scalar field. -/
theorem tensorGaloisAction_mem_baseChange (σ : K ≃ₐ[k] K) (p : Submodule k V)
    (z : K ⊗[k] V) (hz : z ∈ p.baseChange K) :
    tensorGaloisAction σ z ∈ p.baseChange K := by
  rw [Submodule.baseChange_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    simpa only [TensorProduct.mk_apply, tensorGaloisAction_one_tmul] using
      p.tmul_mem_baseChange_of_mem (1 : K) hx
  | zero => simpa only [map_zero] using (p.baseChange K).zero_mem
  | add z z' _ _ hz hz' => simpa only [map_add] using (p.baseChange K).add_mem hz hz'
  | smul c z _ hz =>
    rw [tensorGaloisAction_smul]
    exact (p.baseChange K).smul_mem (σ c) hz

variable {ι : Type t} [Finite ι]

/-- In the scalar-extended basis, the actual tensor action is exactly the
coordinate action used in the descent argument. -/
theorem tensorGaloisAction_coordinates (b : Basis ι k V) (σ : K ≃ₐ[k] K)
    (z : K ⊗[k] V) :
    (b.baseChange K).equivFun (tensorGaloisAction σ z) =
      coordinateGaloisAction σ ((b.baseChange K).equivFun z) := by
  ext i
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    simp only [tensorGaloisAction_tmul, Basis.equivFun_apply, Basis.baseChange_repr_tmul,
      coordinateGaloisAction_apply]
    exact (σ.toLinearEquiv.map_smul (b.repr x i) c).symm
  | add z z' hz hz' =>
    simp only [map_add, Pi.add_apply, coordinateGaloisAction_apply] at *
    rw [hz, hz']

/-- Coordinates of the canonical inclusion use the same basis over k. -/
theorem scalarTensorInclusion_coordinates (b : Basis ι k V) (x : V) :
    (b.baseChange K).equivFun (1 ⊗ₜ[k] x) =
      coordinateScalarInclusion k K ι (b.equivFun x) := by
  ext i
  simp [Basis.equivFun_apply, Algebra.smul_def]

variable [FiniteDimensional k V]

/-- The second assertion of `lem:subspace-descent`, for any subgroup with
fixed scalar field k, on the actual tensor product. -/
theorem tensor_fixed_iff (G : Subgroup (K ≃ₐ[k] K))
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x)
    (z : K ⊗[k] V) :
    (∀ σ : G, tensorGaloisAction σ.val z = z) ↔ ∃ x : V, 1 ⊗ₜ[k] x = z := by
  classical
  let b := Module.Free.chooseBasis k V
  let : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  let e := (b.baseChange K).equivFun
  constructor
  · intro hz
    have hc : ∀ σ : G, coordinateGaloisAction σ.val (e z) = e z := by
      intro σ
      rw [← tensorGaloisAction_coordinates, hz σ]
    obtain ⟨y, hy⟩ := (coordinate_fixed_iff G hG (e z)).mp hc
    refine ⟨b.equivFun.symm y, e.injective ?_⟩
    change (b.baseChange K).equivFun (1 ⊗ₜ[k] b.equivFun.symm y) = e z
    rw [scalarTensorInclusion_coordinates, b.equivFun.apply_symm_apply, hy]
  · rintro ⟨x, rfl⟩ σ
    exact tensorGaloisAction_one_tmul σ.val x

/-- Fixed tensors over the algebraic closure of a perfect field are exactly
the image of the original vector space; no Galois premise is supplied. -/
theorem algebraicClosure_tensor_fixed_iff [PerfectField k] [IsAlgClosure k K]
    (z : K ⊗[k] V) :
    (∀ σ : K ≃ₐ[k] K, tensorGaloisAction σ z = z) ↔ ∃ x : V, 1 ⊗ₜ[k] x = z := by
  constructor
  · intro hz
    have hG : ∀ x : K, (∀ σ : (⊤ : Subgroup (K ≃ₐ[k] K)), σ.val x = x) →
        ∃ c : k, algebraMap k K c = x := by
      intro x hx
      exact (algebraicClosure_fixed_iff x).mp (fun σ => hx ⟨σ, trivial⟩)
    exact (tensor_fixed_iff (⊤ : Subgroup (K ≃ₐ[k] K)) hG z).mp (fun σ => hz σ.val)
  · rintro ⟨x, rfl⟩ σ
    exact tensorGaloisAction_one_tmul σ x

/-- The subspace W₀ in the manuscript, using the canonical tensor inclusion. -/
def descendedTensorSubspace (W : Submodule K (K ⊗[k] V)) : Submodule k V :=
  (W.restrictScalars k).comap (TensorProduct.mk k K V 1)

omit [Finite ι] [FiniteDimensional k V] in
@[simp]
theorem mem_descendedTensorSubspace (W : Submodule K (K ⊗[k] V)) (x : V) :
    x ∈ descendedTensorSubspace W ↔ 1 ⊗ₜ[k] x ∈ W := Iff.rfl

/-- The first assertion of `lem:subspace-descent`: W is the image of
K ⊗[k] W₀ under the actual canonical inclusion. -/
theorem tensor_subspace_descent (G : Subgroup (K ≃ₐ[k] K))
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x)
    (W : Submodule K (K ⊗[k] V))
    (hW : ∀ (σ : G) (z : K ⊗[k] V), z ∈ W → tensorGaloisAction σ.val z ∈ W) :
    W = (descendedTensorSubspace W).baseChange K := by
  classical
  let b := Module.Free.chooseBasis k V
  let : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  let e := (b.baseChange K).equivFun
  let W' := W.map e.toLinearMap
  have hW' : ∀ (σ : G) (x : Module.Free.ChooseBasisIndex k V → K),
      x ∈ W' → coordinateGaloisAction σ.val x ∈ W' := by
    intro σ x hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨tensorGaloisAction σ.val z, hW σ z hz, ?_⟩
    exact tensorGaloisAction_coordinates b σ.val z
  have hdes := coordinate_subspace_descent G hG W' hW'
  apply Submodule.map_injective_of_injective e.injective
  change W' = _
  rw [hdes, Submodule.baseChange_eq_span, Submodule.map_span]
  apply congrArg (Submodule.span K)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨1 ⊗ₜ[k] b.equivFun.symm y, ?_, ?_⟩
    · refine ⟨b.equivFun.symm y, ?_, rfl⟩
      change 1 ⊗ₜ[k] b.equivFun.symm y ∈ W
      have hye : e (1 ⊗ₜ[k] b.equivFun.symm y) ∈ W' := by
        rw [scalarTensorInclusion_coordinates, b.equivFun.apply_symm_apply]
        exact hy
      obtain ⟨z, hz, he⟩ := hye
      rwa [← e.injective he]
    · change (b.baseChange K).equivFun (1 ⊗ₜ[k] b.equivFun.symm y) = _
      rw [scalarTensorInclusion_coordinates, b.equivFun.apply_symm_apply]
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨b.equivFun y, ?_, (scalarTensorInclusion_coordinates b y).symm⟩
    change coordinateScalarInclusion k K _ (b.equivFun y) ∈ W'
    rw [← scalarTensorInclusion_coordinates]
    exact ⟨1 ⊗ₜ[k] y, hy, rfl⟩

/-- Full tensor subspace descent for a perfect base field and its algebraic
closure. The fixed-scalar hypothesis has been discharged, not postulated. -/
theorem algebraicClosure_tensor_subspace_descent [PerfectField k] [IsAlgClosure k K]
    (W : Submodule K (K ⊗[k] V))
    (hW : ∀ (σ : K ≃ₐ[k] K) (z : K ⊗[k] V), z ∈ W → tensorGaloisAction σ z ∈ W) :
    W = (descendedTensorSubspace W).baseChange K := by
  apply tensor_subspace_descent (⊤ : Subgroup (K ≃ₐ[k] K))
  · intro x hx
    exact (algebraicClosure_fixed_iff x).mp (fun σ => hx ⟨σ, trivial⟩)
  · intro σ z hz
    exact hW σ.val z hz

/-- The first assertion of manuscript `lem:subspace-descent`, with the
manuscript's fixed-field equality as its hypothesis. -/
theorem tensor_subspace_descent_of_fixedField (G : Subgroup (K ≃ₐ[k] K))
    (hG : IntermediateField.fixedField G = ⊥)
    (W : Submodule K (K ⊗[k] V))
    (hW : ∀ (σ : G) (z : K ⊗[k] V), z ∈ W → tensorGaloisAction σ.val z ∈ W) :
    W = (descendedTensorSubspace W).baseChange K :=
  tensor_subspace_descent G (fun x => (subgroup_fixed_iff G hG x).mp) W hW

/-- The second assertion of that same lemma with the same fixed-field
hypothesis. -/
theorem tensor_fixed_iff_of_fixedField (G : Subgroup (K ≃ₐ[k] K))
    (hG : IntermediateField.fixedField G = ⊥) (z : K ⊗[k] V) :
    (∀ σ : G, tensorGaloisAction σ.val z = z) ↔ ∃ x : V, 1 ⊗ₜ[k] x = z :=
  tensor_fixed_iff G (fun x => (subgroup_fixed_iff G hG x).mp) z

end

end C3PerfectField
