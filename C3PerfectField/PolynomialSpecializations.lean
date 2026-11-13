module

public import C3PerfectField.ModuleCoefficientTwists
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
Actual specialization modules of a polynomial matrix representation.
An algebra homomorphism into polynomial matrices is the action obtained after
choosing a finite free polynomial basis of the bimodule in `ext:embedding`.
Nothing here asserts that such a representation embedding exists.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped BigOperators ModuleCat Polynomial

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {ι : Type w} [Fintype ι] {κ : Type (max u v)} [Fintype κ] [DecidableEq κ]

/-- Evaluation of all polynomial matrix entries followed by their actual
action on column vectors. -/
def polynomialSpecialization
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    A →ₐ[k] Module.End k (κ → k) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp ((Polynomial.aeval lambda).mapMatrix.comp ρ)

/-- The A-module with action matrix obtained by evaluation at λ. -/
def specializedModule (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    ModuleCat.{max u v} A :=
  letI := Module.compHom (κ → k) (polynomialSpecialization ρ lambda).toRingHom
  ModuleCat.of A (κ → k)

theorem specializedModule_smul (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k)
    (a : A) (x : specializedModule ρ lambda) (r : κ) :
    (a • x) r = ∑ j, (ρ a r j).eval lambda * x j := rfl

/-- The canonical k-action on the bundled A-module agrees with the ordinary
action on column vectors. -/
def specializedScalarEquiv (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    specializedModule ρ lambda ≃ₗ[k] (κ → k) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro c x
    change polynomialSpecialization ρ lambda (algebraMap k A c) x =
      fun j => c * x j
    rw [AlgHom.commutes]
    rfl

theorem finite_specializedModule (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    Module.Finite k (specializedModule ρ lambda) :=
  Module.Finite.equiv (specializedScalarEquiv ρ lambda).symm

theorem finrank_specializedModule (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    Module.finrank k (specializedModule ρ lambda) = Fintype.card κ := by
  rw [(specializedScalarEquiv ρ lambda).finrank_eq]
  exact Module.finrank_fintype_fun_eq_card k

/-- Finite collection of the coefficients of all basis-action polynomials. -/
def polynomialActionCoefficients (bA : Module.Basis ι k A)
    (ρ : A →ₐ[k] Matrix κ κ k[X]) : Finset k := by
  classical
  exact Finset.univ.biUnion (fun irj : ι × κ × κ =>
    (ρ (bA irj.1) irj.2.1 irj.2.2).support.image
      (ρ (bA irj.1) irj.2.1 irj.2.2).coeff)

theorem fixes_polynomialActionCoefficients (bA : Module.Basis ι k A)
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (σ : k ≃+* k)
    (h : ∀ c ∈ polynomialActionCoefficients bA ρ, σ c = c) :
    ∀ i r j n, σ ((ρ (bA i) r j).coeff n) = (ρ (bA i) r j).coeff n := by
  classical
  intro i r j n
  by_cases hn : n ∈ (ρ (bA i) r j).support
  · apply h
    unfold polynomialActionCoefficients
    exact Finset.mem_biUnion.mpr ⟨(i, r, j), Finset.mem_univ _,
      Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  · rw [not_not.mp (mt Polynomial.mem_support_iff.mpr hn), map_zero]

theorem polynomial_eval_fixed_coefficients (σ : k ≃+* k) (p : k[X])
    (h : ∀ n, σ (p.coeff n) = p.coeff n) (lambda : k) :
    σ (p.eval lambda) = p.eval (σ lambda) := by
  have hm : p.map σ.toRingHom = p := by
    ext n
    simpa using h n
  change σ.toRingHom (p.eval lambda) = _
  rw [← Polynomial.eval₂_hom σ.toRingHom, ← Polynomial.eval_map, hm]
  rfl

/-- Coordinate conjugation is semilinear between the two specialized
actions. This checks every algebra element and every vector. -/
theorem specialized_coordinate_action (bA : Module.Basis ι k A)
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (σ : k ≃+* k)
    (h : ∀ i r j n, σ ((ρ (bA i) r j).coeff n) = (ρ (bA i) r j).coeff n)
    (lambda : k) (a : A) (x : κ → k) (r : κ) :
    σ (polynomialSpecialization ρ lambda a x r) =
      polynomialSpecialization ρ (σ lambda) (basisCoordinateAut bA σ a)
        (fun j => σ (x j)) r := by
  have hb (i : ι) (j r : κ) :
      σ ((ρ (bA i) r j).eval lambda) = (ρ (bA i) r j).eval (σ lambda) :=
    polynomial_eval_fixed_coefficients σ _ (h i r j) lambda
  have hx (i : ι) :
      σ (polynomialSpecialization ρ lambda (bA i) x r) =
        polynomialSpecialization ρ (σ lambda) (bA i) (fun j => σ (x j)) r := by
    change σ (∑ j, (ρ (bA i) r j).eval lambda * x j) =
      ∑ j, (ρ (bA i) r j).eval (σ lambda) * σ (x j)
    simp only [map_sum, map_mul, hb]
  conv_lhs => rw [← bA.sum_repr a]
  rw [map_sum]
  conv_rhs => rw [← bA.sum_repr a, map_sum]
  simp only [basisCoordinateAut_smul, basisCoordinateAut_basis, map_sum, map_smul,
    Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, hx]

/-- The actual A-linear isomorphism from the inverse-action twist to
specialization at σ(λ). -/
def specializedTwistIso (bA : Module.Basis ι k A)
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (σ : k ≃+* k)
    (h1 : ∀ i, σ (bA.repr 1 i) = bA.repr 1 i)
    (hm : ∀ i j r, σ (bA.repr (bA i * bA j) r) = bA.repr (bA i * bA j) r)
    (hρ : ∀ i r j n, σ ((ρ (bA i) r j).coeff n) = (ρ (bA i) r j).coeff n)
    (lambda : k) :
    (moduleTwist (basisAlgebraAut bA σ h1 hm)).obj (specializedModule ρ lambda) ≅
      specializedModule ρ (σ lambda) := by
  let α := basisAlgebraAut bA σ h1 hm
  let e : (moduleTwist α).obj (specializedModule ρ lambda) ≃ₗ[A]
      specializedModule ρ (σ lambda) := {
    toFun := fun x j => σ (x j)
    invFun := fun x j => σ.symm (x j)
    left_inv := fun _ => funext fun _ => σ.symm_apply_apply _
    right_inv := fun _ => funext fun _ => σ.apply_symm_apply _
    map_add' := fun _ _ => funext fun _ => map_add σ _ _
    map_smul' := fun a x => by
      apply funext
      intro r
      change σ (polynomialSpecialization ρ lambda (α.symm a) x r) =
        polynomialSpecialization ρ (σ lambda) a (fun j => σ (x j)) r
      rw [specialized_coordinate_action bA ρ σ hρ]
      change polynomialSpecialization ρ (σ lambda) (α (α.symm a)) _ r = _
      rw [α.apply_symm_apply]
  }
  exact e.toModuleIso

/-- A single finitely generated field controls both the finite list and the
entire polynomial family, with the same algebra automorphism action.
The matrix representation is data, not a new hypothesis of the main theorem. -/
theorem exists_coefficientField_polynomialModuleAction [FiniteDimensional k A]
    {η : Type w} [Finite η] (U : η → FiniteModule k A)
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (S : Finset k) :
    ∃ F : Subfield k, Field.FG F ∧ (∀ c ∈ S, c ∈ F) ∧
      ∃ α : (k ≃ₐ[F] k) → (A ≃+* A),
        (∀ σ, IsSemilinearAlgebraAut σ.toRingEquiv (α σ)) ∧
        α (AlgEquiv.refl : k ≃ₐ[F] k) = RingEquiv.refl A ∧
        (∀ σ τ, α (τ.trans σ) = (α τ).trans (α σ)) ∧
        (∀ σ j, Nonempty ((moduleTwist (α σ)).obj (U j).val ≅ (U j).val)) ∧
        ∀ σ lambda, Nonempty ((moduleTwist (α σ)).obj (specializedModule ρ lambda) ≅
          specializedModule ρ (σ lambda)) := by
  classical
  let bA := Module.finBasis k A
  let T := algebraBasisCoefficients bA ∪ (polynomialActionCoefficients bA ρ ∪ S)
  obtain ⟨F, hF, hT, α, hcoord, hα, hid, hcomp, hU⟩ :=
    exists_coefficientField_basisModuleAction bA U T
  refine ⟨F, hF, fun c hc =>
    hT c (Finset.mem_union_right _ (Finset.mem_union_right _ hc)),
    α, hα, hid, hcomp, hU, ?_⟩
  intro σ lambda
  have hfix (c : k) (hc : c ∈ T) : σ c = c := σ.commutes ⟨c, hT c hc⟩
  obtain ⟨h1, hm⟩ := fixes_algebraBasisCoefficients bA σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_left _ hc))
  have hρ := fixes_polynomialActionCoefficients bA ρ σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_right _ (Finset.mem_union_left _ hc)))
  have heq : α σ = basisAlgebraAut bA σ.toRingEquiv h1 hm :=
    RingEquiv.ext (hcoord σ)
  rw [heq]
  exact ⟨specializedTwistIso bA ρ σ.toRingEquiv h1 hm hρ lambda⟩

end

end C3PerfectField
