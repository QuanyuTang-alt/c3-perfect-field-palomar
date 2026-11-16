module

public import C3PerfectField.PolynomialTensorSpecializations
public import C3PerfectField.ARDimension

/-!
The tensor functor and its polynomial representation-embedding contract.
This file proves Lemma `lem:family` from a supplied representation embedding;
it does not prove the stronger polynomial-bimodule existence statement
`ext:embedding`. The contract is not an axiom or a premise of `MainStatement`.

The unconditional main theorem is `C3PerfectField.mainTheorem` in
`C3Integration.lean`. Its proof constructs the sufficient affine-cokernel
family from the proved Kronecker representation embedding, without assuming
this polynomial-tensor contract or claiming its standalone existence theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat Polynomial TensorProduct

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {κ : Type (max u v)} [Fintype κ] [DecidableEq κ]

def polynomialTensorObject (ρ : A →ₐ[k] Matrix κ κ k[X]) (X : ModuleCat.{u} k[X]) :
    ModuleCat.{max u v} A :=
  ModuleCat.of A (polynomialFreeModule ρ ⊗[k[X]] X)

/-- Right freeness gives the dimension formula for every finite source
module, with compatibility of the canonical field actions explicitly checked. -/
def polynomialTensorObjectScalarEquiv (ρ : A →ₐ[k] Matrix κ κ k[X])
    (X : ModuleCat.{u} k[X]) : polynomialTensorObject ρ X ≃ₗ[k] (κ → X) := by
  let e := (TensorProduct.comm k[X] (polynomialFreeModule ρ) X).trans
    (TensorProduct.piScalarRight k[X] k[X] X κ)
  exact {
    toAddEquiv := e.toAddEquiv
    map_smul' := fun c z => by
      change polynomialFreeModule ρ ⊗[k[X]] X at z
      change e (algebraMap k A c • z) = Polynomial.C c • e z
      have h : algebraMap k A c • z = Polynomial.C c • z := by
        induction z using TensorProduct.inductionOn with
        | tmul p x => rw [TensorProduct.smul_tmul', polynomialFreeModule_field_smul,
            TensorProduct.smul_tmul']
        | add z z' hz hz' => simpa only [smul_add] using congrArg₂ (· + ·) hz hz'
      rw [h, map_smul]
  }

theorem finite_polynomialTensorObject (ρ : A →ₐ[k] Matrix κ κ k[X])
    (X : ModuleCat.{u} k[X]) [Module.Finite k X] :
    Module.Finite k (polynomialTensorObject ρ X) :=
  Module.Finite.equiv (polynomialTensorObjectScalarEquiv ρ X).symm

theorem finrank_polynomialTensorObject (ρ : A →ₐ[k] Matrix κ κ k[X])
    (X : ModuleCat.{u} k[X]) [Module.Finite k X] :
    Module.finrank k (polynomialTensorObject ρ X) =
      Fintype.card κ * Module.finrank k X := by
  rw [(polynomialTensorObjectScalarEquiv ρ X).finrank_eq, Module.finrank_pi_fintype]
  simp

def polynomialTensorMap (ρ : A →ₐ[k] Matrix κ κ k[X]) {X Y : ModuleCat.{u} k[X]}
    (f : X ⟶ Y) : polynomialTensorObject ρ X ⟶ polynomialTensorObject ρ Y :=
  ModuleCat.ofHom {
    toAddHom := (TensorProduct.map (LinearMap.id : polynomialFreeModule ρ →ₗ[k[X]] _)
      f.hom).toAddHom
    map_smul' := fun a z => by
      let g := TensorProduct.map (LinearMap.id : polynomialFreeModule ρ →ₗ[k[X]] _) f.hom
      change g (a • z) = a • g z
      induction z using TensorProduct.inductionOn with
      | tmul p x =>
        rw [TensorProduct.smul_tmul' a p x]
        change g ((a • p) ⊗ₜ[k[X]] x) = (a • p) ⊗ₜ[k[X]] f x
        exact TensorProduct.map_tmul _ _ _ _
      | add z z' hz hz' => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hz hz'
  }

@[simp]
theorem polynomialTensorMap_tmul (ρ : A →ₐ[k] Matrix κ κ k[X])
    {X Y : ModuleCat.{u} k[X]} (f : X ⟶ Y) (p : polynomialFreeModule ρ) (x : X) :
    polynomialTensorMap ρ f (p ⊗ₜ[k[X]] x) = p ⊗ₜ[k[X]] f x :=
  TensorProduct.map_tmul _ _ _ _

/-- Tensor with the actual free polynomial A-module. -/
def polynomialTensorFunctor (ρ : A →ₐ[k] Matrix κ κ k[X]) :
    ModuleCat.{u} k[X] ⥤ ModuleCat.{max u v} A where
  obj := polynomialTensorObject ρ
  map := polynomialTensorMap ρ
  map_id X := by
    ext z
    change polynomialTensorMap ρ (𝟙 X) z = z
    change polynomialFreeModule ρ ⊗[k[X]] X at z
    induction z using TensorProduct.inductionOn with
    | tmul p x => simp only [polynomialTensorMap_tmul, ModuleCat.id_apply]
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  map_comp f g := by
    ext z
    change polynomialTensorMap ρ (f ≫ g) z =
      polynomialTensorMap ρ g (polynomialTensorMap ρ f z)
    change polynomialFreeModule ρ ⊗[k[X]] _ at z
    induction z using TensorProduct.inductionOn with
    | tmul p x => simp only [polynomialTensorMap_tmul, ModuleCat.comp_apply]
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'

instance polynomialTensorFunctor_additive (ρ : A →ₐ[k] Matrix κ κ k[X]) :
    (polynomialTensorFunctor ρ).Additive where
  map_add := by
    intro X Y f g
    ext z
    change polynomialTensorMap ρ (f + g) z =
      polynomialTensorMap ρ f z + polynomialTensorMap ρ g z
    change polynomialFreeModule ρ ⊗[k[X]] X at z
    induction z using TensorProduct.inductionOn with
    | tmul p x =>
      rw [polynomialTensorMap_tmul, polynomialTensorMap_tmul, polynomialTensorMap_tmul]
      change p ⊗ₜ[k[X]] (f x + g x) = p ⊗ₜ[k[X]] f x + p ⊗ₜ[k[X]] g x
      exact TensorProduct.tmul_add _ _ _
    | add z z' hz hz' =>
      simp only [map_add, hz, hz']
      abel

/-- The substantive preservation and reflection assertions of `ext:embedding`.
They must be proved for a polynomial action obtained from an arbitrary
representation-infinite algebra before the unconditional main theorem follows. -/
structure IsPolynomialRepresentationEmbedding (ρ : A →ₐ[k] Matrix κ κ k[X]) : Prop where
  preservesIndecomposable :
    ∀ X : ModuleCat.{u} k[X], Module.Finite k X → Indecomposable X →
      Indecomposable ((polynomialTensorFunctor ρ).obj X)
  reflectsIso :
    ∀ X Y : ModuleCat.{u} k[X], Module.Finite k X → Module.Finite k Y →
      Nonempty ((polynomialTensorFunctor ρ).obj X ≅ (polynomialTensorFunctor ρ).obj Y) →
        Nonempty (X ≅ Y)

theorem finite_evaluationQuotientModule (lambda : k) :
    Module.Finite k (evaluationQuotientModule lambda) := by
  let := finite_evaluationModule lambda
  exact Module.Finite.equiv
    ((evaluationQuotientIso lambda).toLinearEquiv.restrictScalars k).symm

theorem IsPolynomialRepresentationEmbedding.indecomposable_family
    {ρ : A →ₐ[k] Matrix κ κ k[X]} (hρ : IsPolynomialRepresentationEmbedding ρ)
    (lambda : k) : Indecomposable (polynomialQuotientTensorModule ρ lambda) :=
  hρ.preservesIndecomposable _ (finite_evaluationQuotientModule lambda)
    (indecomposable_evaluationQuotientModule lambda)

theorem IsPolynomialRepresentationEmbedding.family_iso_iff
    {ρ : A →ₐ[k] Matrix κ κ k[X]} (hρ : IsPolynomialRepresentationEmbedding ρ)
    (lambda mu : k) :
    Nonempty (polynomialQuotientTensorModule ρ lambda ≅
      polynomialQuotientTensorModule ρ mu) ↔ lambda = mu := by
  constructor
  · intro h
    exact (evaluationQuotientModule_iso_iff lambda mu).mp
      (hρ.reflectsIso _ _ (finite_evaluationQuotientModule lambda)
        (finite_evaluationQuotientModule mu) h)
  · rintro rfl
    exact ⟨Iso.refl _⟩

def IsPolynomialRepresentationEmbedding.familyModule
    {ρ : A →ₐ[k] Matrix κ κ k[X]} (hρ : IsPolynomialRepresentationEmbedding ρ)
    (lambda : k) : IndecomposableModule k A :=
  ⟨⟨polynomialQuotientTensorModule ρ lambda, finite_polynomialQuotientTensorModule ρ lambda⟩,
    hρ.indecomposable_family lambda⟩

def IsPolynomialRepresentationEmbedding.familyVertex
    {ρ : A →ₐ[k] Matrix κ κ k[X]} (hρ : IsPolynomialRepresentationEmbedding ρ)
    (lambda : k) : ARVertex k A :=
  Quotient.mk _ (hρ.familyModule lambda)

theorem IsPolynomialRepresentationEmbedding.familyVertex_injective
    {ρ : A →ₐ[k] Matrix κ κ k[X]} (hρ : IsPolynomialRepresentationEmbedding ρ) :
    Function.Injective hρ.familyVertex := by
  intro lambda mu h
  exact (hρ.family_iso_iff lambda mu).mp (Quotient.exact h)

/-- Indecomposability of X_0 forces the polynomial right rank to be positive. -/
theorem IsPolynomialRepresentationEmbedding.rank_pos
    {ρ : A →ₐ[k] Matrix κ κ k[X]} (hρ : IsPolynomialRepresentationEmbedding ρ) :
    0 < Fintype.card κ := by
  have hp := arDimension_pos (hρ.familyVertex (0 : k))
  change 0 < Module.finrank k (polynomialQuotientTensorModule ρ (0 : k)) at hp
  rwa [finrank_polynomialQuotientTensorModule] at hp

end

end C3PerfectField
