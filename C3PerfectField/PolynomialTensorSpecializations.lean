module

public import C3PerfectField.PolynomialSpecializations
public import C3PerfectField.PolynomialEvaluationModules
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
The free polynomial matrix module has a genuine tensor product with S_lambda.
The tensor product is identified A-linearly with the evaluated matrix module.
Thus the previous equivariance and dimension results apply to actual tensors,
not just to a chosen collection of unrelated modules.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat Polynomial TensorProduct BigOperators

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {κ : Type (max u v)} [Fintype κ] [DecidableEq κ]

/-- Free polynomial columns carrying the specified left A-action. -/
def polynomialFreeModule (ρ : A →ₐ[k] Matrix κ κ k[X]) : ModuleCat.{max u v} A :=
  letI := Module.compHom (κ → k[X])
    (Matrix.toLinAlgEquiv'.toRingHom.comp ρ.toRingHom)
  ModuleCat.of A (κ → k[X])

instance polynomialFreeModule_polynomialScalars (ρ : A →ₐ[k] Matrix κ κ k[X]) :
    Module k[X] (polynomialFreeModule ρ) :=
  inferInstanceAs (Module k[X] (κ → k[X]))

instance polynomialFreeModule_smulComm (ρ : A →ₐ[k] Matrix κ κ k[X]) :
    SMulCommClass k[X] A (polynomialFreeModule ρ) where
  smul_comm p a x := by
    change p • (Matrix.toLinAlgEquiv' (ρ a) x) =
      Matrix.toLinAlgEquiv' (ρ a) (p • x)
    exact (map_smul _ p x).symm

theorem polynomialFreeModule_smul (ρ : A →ₐ[k] Matrix κ κ k[X])
    (a : A) (x : polynomialFreeModule ρ) (r : κ) :
    (a • x) r = ∑ j, ρ a r j * x j := rfl

theorem polynomialFreeModule_field_smul (ρ : A →ₐ[k] Matrix κ κ k[X])
    (c : k) (x : polynomialFreeModule ρ) :
    algebraMap k A c • x = Polynomial.C c • x := by
  change Matrix.toLinAlgEquiv' (ρ (algebraMap k A c)) x = Polynomial.C c • x
  rw [AlgHom.commutes]
  change Matrix.toLinAlgEquiv'
    (algebraMap k[X] (Matrix κ κ k[X]) (Polynomial.C c)) x = Polynomial.C c • x
  rw [AlgEquiv.commutes]
  rfl

/-- The actual tensor-product module using the evaluation model of S_lambda. -/
def polynomialTensorModule (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    ModuleCat.{max u v} A :=
  ModuleCat.of A (polynomialFreeModule ρ ⊗[k[X]] evaluationModule lambda)

/-- The canonical free-module tensor coordinates, still polynomial-linear. -/
def polynomialTensorCoordinates (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    polynomialFreeModule ρ ⊗[k[X]] evaluationModule lambda ≃ₗ[k[X]]
      (κ → evaluationModule lambda) :=
  (TensorProduct.comm k[X] _ _).trans
    (TensorProduct.piScalarRight k[X] k[X] (evaluationModule lambda) κ)

theorem polynomialTensorCoordinates_tmul (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k)
    (p : polynomialFreeModule ρ) (x : evaluationModule lambda) (r : κ) :
    polynomialTensorCoordinates ρ lambda (p ⊗ₜ[k[X]] x) r =
      (p r).eval lambda * (show k from x) := by
  change (TensorProduct.piScalarRight k[X] k[X] (evaluationModule lambda) κ)
    (x ⊗ₜ[k[X]] (show κ → k[X] from p)) r = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  exact evaluationModule_smul lambda (p r) x

/-- The tensor coordinates respect the full left A-action. -/
def polynomialTensorSpecializationIso (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    polynomialTensorModule ρ lambda ≅ specializedModule ρ lambda := by
  let e := polynomialTensorCoordinates ρ lambda
  let f : polynomialTensorModule ρ lambda ≃ₗ[A] specializedModule ρ lambda := {
    toAddEquiv := e.toAddEquiv
    map_smul' := fun a z => by
      change e (a • z) = polynomialSpecialization ρ lambda a (e z)
      induction z using TensorProduct.inductionOn with
      | tmul p x =>
        apply funext
        intro r
        rw [TensorProduct.smul_tmul']
        change polynomialTensorCoordinates ρ lambda ((a • p) ⊗ₜ[k[X]] x) r = _
        rw [polynomialTensorCoordinates_tmul]
        change (∑ j, ρ a r j * p j).eval lambda * (show k from x) =
          ∑ j, (ρ a r j).eval lambda *
            (show k from polynomialTensorCoordinates ρ lambda (p ⊗ₜ[k[X]] x) j)
        simp only [polynomialTensorCoordinates_tmul]
        change Polynomial.evalRingHom lambda (∑ j, ρ a r j * p j) * (show k from x) =
          ∑ j, (ρ a r j).eval lambda * ((p j).eval lambda * (show k from x))
        rw [map_sum]
        change (∑ j, (ρ a r j * p j).eval lambda) * (show k from x) = _
        simp only [Polynomial.eval_mul, Finset.sum_mul, mul_assoc]
      | add z z' hz hz' => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hz hz'
  }
  exact f.toModuleIso

theorem finite_polynomialTensorModule (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    Module.Finite k (polynomialTensorModule ρ lambda) := by
  let := finite_specializedModule ρ lambda
  exact Module.Finite.equiv
    ((polynomialTensorSpecializationIso ρ lambda).toLinearEquiv.restrictScalars k).symm

theorem finrank_polynomialTensorModule (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    Module.finrank k (polynomialTensorModule ρ lambda) = Fintype.card κ := by
  rw [((polynomialTensorSpecializationIso ρ lambda).toLinearEquiv.restrictScalars k).finrank_eq,
    finrank_specializedModule]

/-- The literal tensor product with k[T]/(T-lambda), as in the manuscript. -/
def polynomialQuotientTensorModule (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    ModuleCat.{max u v} A :=
  ModuleCat.of A (polynomialFreeModule ρ ⊗[k[X]] evaluationQuotientModule lambda)

def polynomialQuotientTensorIso (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    polynomialQuotientTensorModule ρ lambda ≅ polynomialTensorModule ρ lambda := by
  let e := TensorProduct.congr (LinearEquiv.refl k[X] (polynomialFreeModule ρ))
    (evaluationQuotientIso lambda).toLinearEquiv
  let f : polynomialQuotientTensorModule ρ lambda ≃ₗ[A] polynomialTensorModule ρ lambda := {
    toAddEquiv := e.toAddEquiv
    map_smul' := fun a z => by
      change e (a • z) = a • e z
      induction z using TensorProduct.inductionOn with
      | tmul p x =>
        rw [TensorProduct.smul_tmul' a p x]
        change e ((a • p) ⊗ₜ[k[X]] x) =
          (a • p) ⊗ₜ[k[X]] (evaluationQuotientIso lambda).toLinearEquiv x
        exact TensorProduct.congr_tmul _ _ _ _
      | add z z' hz hz' => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hz hz'
  }
  exact f.toModuleIso

def polynomialQuotientTensorSpecializationIso
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    polynomialQuotientTensorModule ρ lambda ≅ specializedModule ρ lambda :=
  polynomialQuotientTensorIso ρ lambda ≪≫ polynomialTensorSpecializationIso ρ lambda

theorem finite_polynomialQuotientTensorModule
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    Module.Finite k (polynomialQuotientTensorModule ρ lambda) := by
  let := finite_specializedModule ρ lambda
  exact Module.Finite.equiv
    ((polynomialQuotientTensorSpecializationIso ρ lambda).toLinearEquiv.restrictScalars k).symm

theorem finrank_polynomialQuotientTensorModule
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (lambda : k) :
    Module.finrank k (polynomialQuotientTensorModule ρ lambda) = Fintype.card κ := by
  rw [((polynomialQuotientTensorSpecializationIso ρ lambda).toLinearEquiv.restrictScalars k).finrank_eq,
    finrank_specializedModule]

/-- The coefficient-field conclusion for actual quotient tensor modules,
using the very same action that fixes the prescribed finite list. -/
theorem exists_coefficientField_polynomialTensorAction [FiniteDimensional k A]
    {η : Type w} [Finite η] (U : η → FiniteModule k A)
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (S : Finset k) :
    ∃ F : Subfield k, Field.FG F ∧ (∀ c ∈ S, c ∈ F) ∧
      ∃ α : (k ≃ₐ[F] k) → (A ≃+* A),
        (∀ σ, IsSemilinearAlgebraAut σ.toRingEquiv (α σ)) ∧
        α (AlgEquiv.refl : k ≃ₐ[F] k) = RingEquiv.refl A ∧
        (∀ σ τ, α (τ.trans σ) = (α τ).trans (α σ)) ∧
        (∀ σ j, Nonempty ((moduleTwist (α σ)).obj (U j).val ≅ (U j).val)) ∧
        ∀ σ lambda,
          Nonempty ((moduleTwist (α σ)).obj (polynomialQuotientTensorModule ρ lambda) ≅
            polynomialQuotientTensorModule ρ (σ lambda)) := by
  obtain ⟨F, hF, hS, α, hα, hid, hcomp, hU, hρ⟩ :=
    exists_coefficientField_polynomialModuleAction U ρ S
  refine ⟨F, hF, hS, α, hα, hid, hcomp, hU, ?_⟩
  intro σ lambda
  obtain ⟨e⟩ := hρ σ lambda
  exact ⟨(moduleTwist (α σ)).mapIso (polynomialQuotientTensorSpecializationIso ρ lambda) ≪≫
    e ≪≫ (polynomialQuotientTensorSpecializationIso ρ (σ lambda)).symm⟩

end

end C3PerfectField
