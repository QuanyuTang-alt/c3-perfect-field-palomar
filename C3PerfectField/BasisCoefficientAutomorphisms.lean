module

public import C3PerfectField.SemilinearTwisting
public import C3PerfectField.CoefficientFields
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
The algebra-automorphism step in manuscript Lemma `lem:coefficient-field`.
The coefficient list includes the coordinates of 1, so any finite basis
works without a special basis-choice assumption.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open scoped BigOperators ModuleCat

universe u v w

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
  {ι : Type w}

/-- Apply the field automorphism to each coordinate in an actual basis. -/
def basisCoordinateAut (b : Module.Basis ι k V) (σ : k ≃+* k) : V ≃+ V :=
  (b.repr.toAddEquiv.trans (Finsupp.mapRange.addEquiv σ.toAddEquiv)).trans
    b.repr.symm.toAddEquiv

@[simp]
theorem basisCoordinateAut_repr (b : Module.Basis ι k V) (σ : k ≃+* k)
    (x : V) (i : ι) : b.repr (basisCoordinateAut b σ x) i = σ (b.repr x i) := by
  simp [basisCoordinateAut]

theorem basisCoordinateAut_smul (b : Module.Basis ι k V) (σ : k ≃+* k)
    (c : k) (x : V) :
    basisCoordinateAut b σ (c • x) = σ c • basisCoordinateAut b σ x := by
  apply b.repr.injective
  ext i
  simp [map_mul]

@[simp]
theorem basisCoordinateAut_basis (b : Module.Basis ι k V) (σ : k ≃+* k) (i : ι) :
    basisCoordinateAut b σ (b i) = b i := by
  classical
  apply b.repr.injective
  ext j
  simp [Finsupp.single_apply, apply_ite]

theorem basisCoordinateAut_fixed (b : Module.Basis ι k V) (σ : k ≃+* k)
    (x : V) (h : ∀ i, σ (b.repr x i) = b.repr x i) :
    basisCoordinateAut b σ x = x := by
  apply b.repr.injective
  ext i
  exact (basisCoordinateAut_repr b σ x i).trans (h i)

@[simp]
theorem basisCoordinateAut_refl (b : Module.Basis ι k V) :
    basisCoordinateAut b (RingEquiv.refl k) = AddEquiv.refl V := by
  apply AddEquiv.ext
  intro x
  apply b.repr.injective
  ext i
  simp

theorem basisCoordinateAut_trans (b : Module.Basis ι k V) (σ τ : k ≃+* k) :
    basisCoordinateAut b (τ.trans σ) =
      (basisCoordinateAut b τ).trans (basisCoordinateAut b σ) := by
  apply AddEquiv.ext
  intro x
  apply b.repr.injective
  ext i
  simp

variable {A : Type v} [Ring A] [Algebra k A] [Fintype ι]

/-- Fixed structure constants make coordinate conjugation multiplicative. -/
theorem basisCoordinateAut_mul (b : Module.Basis ι k A) (σ : k ≃+* k)
    (h : ∀ i j r, σ (b.repr (b i * b j) r) = b.repr (b i * b j) r)
    (x y : A) : basisCoordinateAut b σ (x * y) =
      basisCoordinateAut b σ x * basisCoordinateAut b σ y := by
  have hp (i j : ι) : basisCoordinateAut b σ (b i * b j) = b i * b j :=
    basisCoordinateAut_fixed b σ _ (h i j)
  have hy (i : ι) : basisCoordinateAut b σ (b i * y) =
      b i * basisCoordinateAut b σ y := by
    conv_lhs => rw [← b.sum_repr y, Finset.mul_sum]
    rw [map_sum]
    conv_rhs => rw [← b.sum_repr y, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.mul_smul_comm, basisCoordinateAut_smul, hp,
      basisCoordinateAut_smul, Algebra.mul_smul_comm, basisCoordinateAut_basis]
  conv_lhs => rw [← b.sum_repr x, Finset.sum_mul]
  rw [map_sum]
  conv_rhs => rw [← b.sum_repr x, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_mul_assoc, basisCoordinateAut_smul, hy,
    basisCoordinateAut_smul, Algebra.smul_mul_assoc, basisCoordinateAut_basis]

/-- The actual ring automorphism determined by fixed unit and product coefficients. -/
def basisAlgebraAut (b : Module.Basis ι k A) (σ : k ≃+* k)
    (_h1 : ∀ i, σ (b.repr 1 i) = b.repr 1 i)
    (hm : ∀ i j r, σ (b.repr (b i * b j) r) = b.repr (b i * b j) r) :
    A ≃+* A where
  toAddEquiv := basisCoordinateAut b σ
  map_mul' := basisCoordinateAut_mul b σ hm

theorem basisAlgebraAut_semilinear (b : Module.Basis ι k A) (σ : k ≃+* k)
    (h1 : ∀ i, σ (b.repr 1 i) = b.repr 1 i)
    (hm : ∀ i j r, σ (b.repr (b i * b j) r) = b.repr (b i * b j) r) :
    IsSemilinearAlgebraAut σ (basisAlgebraAut b σ h1 hm) := by
  intro c
  change basisCoordinateAut b σ (algebraMap k A c) = algebraMap k A (σ c)
  simpa only [Algebra.smul_def, mul_one] using
    (basisCoordinateAut_smul b σ c (1 : A)).trans
      (congrArg (fun x : A => σ c • x) (basisCoordinateAut_fixed b σ 1 h1))

/-- The finitely many algebra coefficients, with no basis containing 1 required. -/
def algebraBasisCoefficients (b : Module.Basis ι k A) : Finset k := by
  classical
  exact Finset.univ.image (fun i => b.repr 1 i) ∪
    Finset.univ.image (fun ijr : ι × ι × ι => b.repr (b ijr.1 * b ijr.2.1) ijr.2.2)

theorem fixes_algebraBasisCoefficients (b : Module.Basis ι k A) (σ : k ≃+* k)
    (h : ∀ c ∈ algebraBasisCoefficients b, σ c = c) :
    (∀ i, σ (b.repr 1 i) = b.repr 1 i) ∧
      ∀ i j r, σ (b.repr (b i * b j) r) = b.repr (b i * b j) r := by
  classical
  constructor
  · intro i
    apply h
    unfold algebraBasisCoefficients
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · intro i j r
    apply h
    unfold algebraBasisCoefficients
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j, r),
      Finset.mem_univ _, rfl⟩)

end

end C3PerfectField
