module

public import C3PerfectField.SeparableTensorModules
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
Finite fields of definition by action coefficients, as in manuscript
`lem:finite-model`. A model is the subspace whose coordinates belong to
the intermediate field. This avoids assuming the matrix relations:
the action is restricted from the original representation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open scoped TensorProduct BigOperators

universe u v w z

variable {k K : Type u} {N : Type v} [Field k] [Field K] [Algebra k K]
  [AddCommGroup N] [Module K N] [Module k N] [IsScalarTower k K N]
  {κ : Type w} [Fintype κ] (b : Module.Basis κ K N) (L : IntermediateField k K)

/-- The actual L-vector subspace consisting of vectors with coordinates in L. -/
def basisModelSubspace : Submodule L N where
  carrier := {x | ∀ i, b.repr x i ∈ L}
  zero_mem' := by
    intro i
    simpa only [map_zero, Finsupp.zero_apply] using L.zero_mem
  add_mem' := by
    intro x y hx hy i
    simpa only [map_add, Finsupp.add_apply] using L.add_mem (hx i) (hy i)
  smul_mem' := by
    intro r x hx i
    rw [← IsScalarTower.algebraMap_smul K r x, map_smul]
    exact L.mul_mem r.property (hx i)

/-- Coordinate restriction is an L-linear equivalence to the finite coordinate space. -/
def basisModelCoordinateEquiv : basisModelSubspace b L ≃ₗ[L] (κ → L) where
  toFun x i := ⟨b.repr x.val i, x.property i⟩
  invFun y := ⟨b.equivFun.symm (fun i => (y i : K)), by
    intro i
    change b.equivFun (b.equivFun.symm (fun i => (y i : K))) i ∈ L
    rw [b.equivFun.apply_symm_apply]
    exact (y i).property⟩
  left_inv x := by
    apply Subtype.ext
    exact b.equivFun.symm_apply_apply x.val
  right_inv y := by
    ext i
    exact congrFun (b.equivFun.apply_symm_apply (fun i => (y i : K))) i
  map_add' x y := by
    ext i
    exact DFunLike.congr_fun (b.repr.map_add x.val y.val) i
  map_smul' r x := by
    ext i
    change b.repr (r • x.val) i = (r : K) * b.repr x.val i
    rw [← IsScalarTower.algebraMap_smul K r x.val, map_smul]
    rfl

omit [Module k N] [IsScalarTower k K N] in
/-- The coefficient model is finite-dimensional over L. -/
theorem finite_basisModelSubspace : Module.Finite L (basisModelSubspace b L) :=
  Module.Finite.equiv (basisModelCoordinateEquiv b L).symm

omit [Module k N] [IsScalarTower k K N] [Fintype κ] in
/-- Every original basis vector belongs to the coefficient model. -/
theorem basis_mem_basisModelSubspace (i : κ) : b i ∈ basisModelSubspace b L := by
  classical
  intro j
  simp only [b.repr_self, Finsupp.single_apply]
  split_ifs
  · exact L.one_mem
  · exact L.zero_mem

/-- A finite L-basis of the actual coefficient subspace. -/
def basisModelBasis : Module.Basis κ L (basisModelSubspace b L) :=
  (Pi.basisFun L κ).map (basisModelCoordinateEquiv b L).symm

omit [Module k N] [IsScalarTower k K N] in
@[simp]
theorem basisModelBasis_val (i : κ) : (basisModelBasis b L i : N) = b i := by
  classical
  apply b.equivFun.injective
  ext j
  change b.equivFun (b.equivFun.symm _) j = b.repr (b i) j
  rw [b.equivFun.apply_symm_apply, b.repr_self]
  by_cases h : i = j
  · subst j
    simp
  · simp [Ne.symm h]

/-- Extending this finite coordinate basis recovers the original vector space. -/
def basisModelExtensionEquiv : (K ⊗[L] basisModelSubspace b L) ≃ₗ[K] N :=
  ((basisModelBasis b L).baseChange K).equiv b (Equiv.refl κ)

omit [Module k N] [IsScalarTower k K N] in
/-- The extension equivalence is the actual tensor inclusion into N. -/
theorem basisModelExtensionEquiv_tmul (c : K) (x : basisModelSubspace b L) :
    basisModelExtensionEquiv b L (c ⊗ₜ[L] x) = c • (x : N) := by
  have he : (basisModelExtensionEquiv b L).toLinearMap =
      (basisModelSubspace b L).subtype.liftBaseChange K := by
    apply ((basisModelBasis b L).baseChange K).ext
    intro i
    rw [LinearEquiv.coe_toLinearMap, basisModelExtensionEquiv, Module.Basis.equiv_apply,
      Equiv.refl_apply, Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul,
      Submodule.subtype_apply, basisModelBasis_val, one_smul]
  exact LinearMap.congr_fun he (c ⊗ₜ[L] x)

variable {A : Type z} [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] (bA : Module.Basis ι k A)
  (ρ : A →ₐ[k] Module.End K N)

/-- The finite set of all action-matrix coefficients on the chosen bases. -/
def finiteModelCoefficients : Finset K := by
  classical
  exact Finset.univ.image (fun ijr : ι × κ × κ =>
    b.repr (ρ (bA ijr.1) (b ijr.2.1)) ijr.2.2)

omit [Fintype ι] in
/-- Basis actions preserve the model whenever their matrix entries belong to L. -/
theorem basisModelSubspace_basisAction
    (hc : ∀ i j r, b.repr (ρ (bA i) (b j)) r ∈ L)
    (i : ι) (x : N) (hx : x ∈ basisModelSubspace b L) :
    ρ (bA i) x ∈ basisModelSubspace b L := by
  intro r
  rw [← b.sum_repr x, map_sum, map_sum]
  simp only [map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  apply L.sum_mem
  intro j _
  exact L.mul_mem (hx j) (hc i j r)

/-- The full A-action preserves the model, including arbitrary k-linear combinations. -/
theorem basisModelSubspace_action
    (hc : ∀ i j r, b.repr (ρ (bA i) (b j)) r ∈ L)
    (a : A) (x : N) (hx : x ∈ basisModelSubspace b L) :
    ρ a x ∈ basisModelSubspace b L := by
  have hb := basisModelSubspace_basisAction b L bA ρ hc
  intro r
  rw [← bA.sum_repr a, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [map_sum, Finset.sum_apply']
  apply L.sum_mem
  intro i _
  rw [← IsScalarTower.algebraMap_smul K (bA.repr a i) (ρ (bA i) x), map_smul]
  exact L.mul_mem (L.algebraMap_mem _) (hb i x hx r)

include bA in
/-- Adjoining the finitely many algebraic action coefficients gives a finite
intermediate field whose coordinate model is stable under the full action. -/
theorem exists_finite_basisModel [Algebra.IsAlgebraic k K] :
    ∃ L : IntermediateField k K, Module.Finite k L ∧
      ∀ a x, x ∈ basisModelSubspace b L → ρ a x ∈ basisModelSubspace b L := by
  classical
  let S := finiteModelCoefficients b bA ρ
  let L := IntermediateField.adjoin k (S : Set K)
  have hfin : Module.Finite k L :=
    IntermediateField.finiteDimensional_adjoin (fun c _ =>
      (Algebra.IsAlgebraic.isAlgebraic c).isIntegral)
  refine ⟨L, hfin, basisModelSubspace_action b L bA ρ ?_⟩
  intro i j r
  apply IntermediateField.subset_adjoin k (S : Set K)
  exact Finset.mem_image.mpr ⟨(i, j, r), Finset.mem_univ _, rfl⟩

variable (h : ∀ a x, x ∈ basisModelSubspace b L → ρ a x ∈ basisModelSubspace b L)

/-- The intermediate field action and the existing base-field action agree. -/
instance basisModelIntermediateTower : IsScalarTower k L N :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change algebraMap k K c • x = c • x
    exact IsScalarTower.algebraMap_smul K c x

/-- Restriction of the original action; all algebra relations are inherited. -/
def basisModelAction : A →ₐ[k] Module.End L (basisModelSubspace b L) where
  toFun a := {
    toFun x := ⟨ρ a x.val, h a x.val x.property⟩
    map_add' x y := Subtype.ext ((ρ a).map_add x.val y.val)
    map_smul' r x := Subtype.ext (((ρ a).restrictScalars L).map_smul r x.val)
  }
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun ρ.map_one x.val
  map_mul' a a' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (ρ.map_mul a a') x.val
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun ρ.map_zero x.val
  map_add' a a' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (ρ.map_add a a') x.val
  commutes' r := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (ρ.commutes r) x.val

omit [Fintype κ] in
@[simp]
theorem basisModelAction_apply_val (a : A) (x : basisModelSubspace b L) :
    (basisModelAction b L ρ h a x : N) = ρ a (x : N) := rfl

/-- Extend the restricted action to the original tensor algebra A_K. -/
def basisModelTensorRepresentation :
    (K ⊗[k] A) →ₐ[K] Module.End K (K ⊗[L] basisModelSubspace b L) :=
  AlgHom.liftEquiv k K A _
    (((Module.End.baseChangeHom L K (basisModelSubspace b L)).restrictScalars k).comp
      (basisModelAction b L ρ h))

omit [Fintype κ] in
theorem basisModelTensorRepresentation_tmul (c d : K) (a : A)
    (x : basisModelSubspace b L) :
    basisModelTensorRepresentation b L ρ h (c ⊗ₜ[k] a) (d ⊗ₜ[L] x) =
      (c * d) ⊗ₜ[L] (basisModelAction b L ρ h a x) := by
  change c • ((basisModelAction b L ρ h a).baseChange K) (d ⊗ₜ[L] x) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  rfl

/-- Scalar extension recovers the original full algebra action on all tensors. -/
theorem basisModelExtensionEquiv_algebraAction (s : K ⊗[k] A)
    (z : K ⊗[L] basisModelSubspace b L) :
    basisModelExtensionEquiv b L (basisModelTensorRepresentation b L ρ h s z) =
      (AlgHom.liftEquiv k K A _ ρ s) (basisModelExtensionEquiv b L z) := by
  induction s using TensorProduct.inductionOn with
  | tmul c a =>
    induction z using TensorProduct.inductionOn with
    | tmul d x =>
      rw [basisModelTensorRepresentation_tmul, basisModelExtensionEquiv_tmul,
        basisModelExtensionEquiv_tmul, AlgHom.liftEquiv_tmul, LinearMap.smul_apply,
        map_smul, smul_smul]
      rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  | add s s' hs hs' => simp only [map_add, LinearMap.add_apply, hs, hs']

end

end C3PerfectField
