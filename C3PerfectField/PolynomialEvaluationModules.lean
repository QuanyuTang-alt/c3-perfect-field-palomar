module

public import C3PerfectField.MainStatement
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.LinearAlgebra.Dimension.Finite
public import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
The actual simple evaluation modules in manuscript Lemma `lem:family`.
The module obtained by evaluation is identified with k[T]/(T-lambda);
its indecomposability, dimension and parameter classification are proved.
No representation embedding is asserted here.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat Polynomial

universe u

variable {k : Type u} [Field k]

/-- k with p(T) acting by multiplication by p(lambda). -/
def evaluationModule (lambda : k) : ModuleCat.{u} k[X] :=
  letI := Module.compHom k (Polynomial.evalRingHom lambda)
  ModuleCat.of k[X] k

theorem evaluationModule_smul (lambda : k) (p : k[X]) (x : evaluationModule lambda) :
    p • x = p.eval lambda * (show k from x) := rfl

/-- This is the manuscript's literal quotient module S_lambda. -/
def evaluationQuotientModule (lambda : k) : ModuleCat.{u} k[X] :=
  ModuleCat.of k[X] (k[X] ⧸ Ideal.span ({Polynomial.X - Polynomial.C lambda} : Set k[X]))

/-- Evaluation gives the required polynomial-linear, not merely field-linear,
identification of the quotient with the evaluation module. -/
def evaluationQuotientIso (lambda : k) :
    evaluationQuotientModule lambda ≅ evaluationModule lambda := by
  let e := Polynomial.quotientSpanXSubCAlgEquiv lambda
  let f : evaluationQuotientModule lambda ≃ₗ[k[X]] evaluationModule lambda := {
    toAddEquiv := e.toAddEquiv
    map_smul' := fun p x => by
      change k[X] ⧸ Ideal.span ({Polynomial.X - Polynomial.C lambda} : Set k[X]) at x
      change e (Ideal.Quotient.mk _ p * x) = p.eval lambda * e x
      rw [map_mul, Polynomial.quotientSpanXSubCAlgEquiv_mk]
  }
  exact f.toModuleIso

/-- Compatibility with the canonical k-action of the bundled module. -/
def evaluationScalarEquiv (lambda : k) : evaluationModule lambda ≃ₗ[k] k where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro c x
    change k at x
    change (Polynomial.C c).eval lambda * x = c * x
    rw [Polynomial.eval_C]

theorem finite_evaluationModule (lambda : k) : Module.Finite k (evaluationModule lambda) :=
  Module.Finite.equiv (evaluationScalarEquiv lambda).symm

theorem finrank_evaluationModule (lambda : k) :
    Module.finrank k (evaluationModule lambda) = 1 := by
  rw [(evaluationScalarEquiv lambda).finrank_eq, Module.finrank_self]

theorem evaluationModule_hom_apply {lambda mu : k}
    (f : evaluationModule lambda ⟶ evaluationModule mu) (x : evaluationModule lambda) :
    f x = (show k from x) * (show k from f (1 : k)) := by
  have h := f.hom.map_smul (Polynomial.C (show k from x)) (1 : k)
  simpa only [evaluationModule_smul, Polynomial.eval_C, mul_one,
    RingHom.id_apply] using h

theorem indecomposable_evaluationModule (lambda : k) :
    Indecomposable (evaluationModule lambda) := by
  apply TauCeti.indecomposable_of_injective_of_isLocalRing
    (fun f : evaluationModule lambda ⟶ evaluationModule lambda => (show k from f (1 : k)))
  · intro f g hfg
    change (show k from f (1 : k)) = (show k from g (1 : k)) at hfg
    ext x
    rw [evaluationModule_hom_apply f, evaluationModule_hom_apply g]
    exact congrArg (fun c : k => (show k from x) * c) hfg
  · rfl
  · rfl
  · intro f
    change f (f (1 : k)) = (show k from f (1 : k)) * (show k from f (1 : k))
    exact evaluationModule_hom_apply f _

theorem evaluationModule_iso_iff (lambda mu : k) :
    Nonempty (evaluationModule lambda ≅ evaluationModule mu) ↔ lambda = mu := by
  constructor
  · rintro ⟨e⟩
    have hc : (show k from e.hom (1 : k)) ≠ 0 := by
      intro hh
      have h0 : e.hom (1 : k) = e.hom (0 : k) := by
        simpa only [map_zero] using hh
      have h10 := e.toLinearEquiv.injective h0
      exact one_ne_zero (show (1 : k) = 0 from h10)
    have h := e.hom.hom.map_smul Polynomial.X (1 : k)
    have h' : e.hom (lambda : k) = mu * (show k from e.hom (1 : k)) := by
      simpa only [evaluationModule_smul, Polynomial.eval_X, mul_one,
        RingHom.id_apply] using h
    have heq : lambda * (show k from e.hom (1 : k)) =
        mu * (show k from e.hom (1 : k)) := by
      exact (evaluationModule_hom_apply e.hom (lambda : k)).symm.trans h'
    exact mul_right_cancel₀ hc heq
  · rintro rfl
    exact ⟨Iso.refl _⟩

theorem evaluationQuotientModule_iso_iff (lambda mu : k) :
    Nonempty (evaluationQuotientModule lambda ≅ evaluationQuotientModule mu) ↔
      lambda = mu := by
  constructor
  · rintro ⟨e⟩
    exact (evaluationModule_iso_iff lambda mu).mp
      ⟨(evaluationQuotientIso lambda).symm ≪≫ e ≪≫ evaluationQuotientIso mu⟩
  · rintro rfl
    exact ⟨Iso.refl _⟩

theorem indecomposable_evaluationQuotientModule (lambda : k) :
    Indecomposable (evaluationQuotientModule lambda) :=
  (indecomposable_evaluationModule lambda).of_iso (evaluationQuotientIso lambda).symm

theorem finrank_evaluationQuotientModule (lambda : k) :
    Module.finrank k (evaluationQuotientModule lambda) = 1 := by
  rw [((evaluationQuotientIso lambda).toLinearEquiv.restrictScalars k).finrank_eq,
    finrank_evaluationModule]

end

end C3PerfectField
