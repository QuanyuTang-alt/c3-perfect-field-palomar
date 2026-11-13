module

public import C3PerfectField.SemilinearTwisting
public import C3PerfectField.Radicals
public import C3PerfectField.ARDimension
public import C3PerfectField.UniformLocalBound
public import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
Semilinear twisting acts on the actual Auslander--Reiten vertices, preserves
the radical and its square, and therefore preserves arrows and dimensions.
Intermediate modules in the radical square retain their field finiteness.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {σ : k ≃+* k} {α : A ≃+* A}

theorem indecomposable_moduleTwist (α : A ≃+* A)
    {X : ModuleCat.{max u v} A} (hX : Indecomposable X) :
    Indecomposable ((moduleTwist α).obj X) :=
  Functor.indecomposable_obj_of_map_bijective (moduleTwist α) hX
    ((moduleTwistEquivalence α).fullyFaithfulFunctor.map_bijective X X)

def twistFiniteModule (h : IsSemilinearAlgebraAut σ α) (X : FiniteModule k A) :
    FiniteModule k A := by
  letI := X.property
  exact ⟨(moduleTwist α).obj X.val, moduleTwist_finite h X.val⟩

def twistIndecomposableModule (h : IsSemilinearAlgebraAut σ α)
    (X : IndecomposableModule k A) : IndecomposableModule k A :=
  ⟨twistFiniteModule h X.val, indecomposable_moduleTwist α X.property⟩

theorem isRadical_moduleTwist_iff (α : A ≃+* A)
    {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y) :
    IsRadical A ((moduleTwist α).map f) ↔ IsRadical A f := by
  let F := moduleTwist α
  have heq (g : Y ⟶ X) :
      F.map (𝟙 X - f ≫ g) = 𝟙 (F.obj X) - F.map f ≫ F.map g := by
    rw [F.map_sub, F.map_comp, F.map_id]
  constructor
  · intro hf g
    have hi : IsIso (F.map (𝟙 X - f ≫ g)) := by
      rw [heq]
      exact hf (F.map g)
    let := hi
    exact isIso_of_reflects_iso (𝟙 X - f ≫ g) F
  · intro hf g
    obtain ⟨g', rfl⟩ := F.map_surjective g
    let := hf g'
    rw [← heq]
    exact
      (inferInstance : IsIso (F.map (𝟙 X - f ≫ g')))

theorem IsRadicalSquare.twist (h : IsSemilinearAlgebraAut σ α)
    {X Y : ModuleCat.{max u v} A} {f : X ⟶ Y} (hf : IsRadicalSquare k A f) :
    IsRadicalSquare k A ((moduleTwist α).map f) := by
  obtain ⟨n, W, a, b, hab, heq⟩ := hf
  refine ⟨n, fun j => twistFiniteModule h (W j),
    fun j => (moduleTwist α).map (a j),
    fun j => (moduleTwist α).map (b j),
    fun j => ⟨(isRadical_moduleTwist_iff α _).mpr (hab j).1,
      (isRadical_moduleTwist_iff α _).mpr (hab j).2⟩, ?_⟩
  rw [heq, Functor.map_sum]
  simp only [Functor.map_comp]

theorem isRadicalSquare_moduleTwist_iff (h : IsSemilinearAlgebraAut σ α)
    {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y) :
    IsRadicalSquare k A ((moduleTwist α).map f) ↔ IsRadicalSquare k A f := by
  constructor
  · intro hf
    have hi := hf.twist h.symm
    let e := (moduleTwistEquivalence α).unitIso.app X
    let d := ((moduleTwistEquivalence α).unitIso.app Y).symm
    have heq : e.hom ≫ (moduleTwist α.symm).map ((moduleTwist α).map f) ≫ d.hom = f := by
      ext x
      rfl
    rw [← heq]
    exact (isRadicalSquare_iso_iff e d _).mpr hi
  · exact fun hf => hf.twist h

theorem hasARArrow_twist_iff (h : IsSemilinearAlgebraAut σ α)
    (X Y : IndecomposableModule k A) :
    HasARArrow k A (twistIndecomposableModule h X) (twistIndecomposableModule h Y) ↔
      HasARArrow k A X Y := by
  constructor
  · rintro ⟨f, hf, hf2⟩
    obtain ⟨f', rfl⟩ := (moduleTwist α).map_surjective f
    exact ⟨f', (isRadical_moduleTwist_iff α _).mp hf,
      fun hh => hf2 ((isRadicalSquare_moduleTwist_iff h _).mpr hh)⟩
  · rintro ⟨f, hf, hf2⟩
    exact ⟨(moduleTwist α).map f, (isRadical_moduleTwist_iff α _).mpr hf,
      fun hh => hf2 ((isRadicalSquare_moduleTwist_iff h _).mp hh)⟩

/-- Twisting descends to the genuine quotient of module isomorphism classes. -/
def arTwist (h : IsSemilinearAlgebraAut σ α) : ARVertex k A → ARVertex k A :=
  Quotient.map (twistIndecomposableModule h) (fun _ _ ⟨e⟩ =>
    ⟨(moduleTwist α).mapIso e⟩)

@[simp]
theorem arTwist_mk (h : IsSemilinearAlgebraAut σ α) (X : IndecomposableModule k A) :
    arTwist h (Quotient.mk _ X) = Quotient.mk _ (twistIndecomposableModule h X) := rfl

def arTwistEquiv (h : IsSemilinearAlgebraAut σ α) : ARVertex k A ≃ ARVertex k A where
  toFun := arTwist h
  invFun := arTwist h.symm
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h X =>
      apply Quotient.sound
      exact ⟨((moduleTwistEquivalence α).unitIso.app X.obj).symm⟩
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h X =>
      apply Quotient.sound
      exact ⟨((moduleTwistEquivalence α.symm).unitIso.app X.obj).symm⟩

theorem arArrow_twist_iff (h : IsSemilinearAlgebraAut σ α) (x y : ARVertex k A) :
    ARArrow k A (arTwist h x) (arTwist h y) ↔ ARArrow k A x y := by
  induction x using Quotient.inductionOn with
  | h X =>
    induction y using Quotient.inductionOn with
    | h Y =>
      simp only [arTwist_mk, arArrow_mk_iff]
      exact hasARArrow_twist_iff h X Y

theorem arDimension_twist (h : IsSemilinearAlgebraAut σ α) (x : ARVertex k A) :
    arDimension (arTwist h x) = arDimension x := by
  induction x using Quotient.inductionOn with
  | h X =>
    exact moduleTwist_finrank h X.obj

theorem arTwist_refl (h : IsSemilinearAlgebraAut σ (RingEquiv.refl A))
    (x : ARVertex k A) : arTwist h x = x := by
  induction x using Quotient.inductionOn with
  | h X =>
    apply Quotient.sound
    exact ⟨moduleTwistId.app X.obj⟩

theorem arTwist_trans {τ : k ≃+* k} {β : A ≃+* A}
    (hα : IsSemilinearAlgebraAut σ α) (hβ : IsSemilinearAlgebraAut τ β)
    (x : ARVertex k A) :
    arTwist hα (arTwist hβ x) = arTwist (hα.trans hβ) x := by
  induction x using Quotient.inductionOn with
  | h X =>
    apply Quotient.sound
    exact ⟨(moduleTwistComp α β).app X.obj⟩

/-- The twist meets the precise automorphism contract of the already
proved weighted-graph period argument. -/
def arWeightedTwist [FiniteDimensional k A] (h : IsSemilinearAlgebraAut σ α) :
    (arWeightedDigraph (k := k) (A := A)).Automorphism where
  perm := arTwistEquiv h
  arrow_iff := arArrow_twist_iff h
  weight_eq := arDimension_twist h

end

end C3PerfectField
