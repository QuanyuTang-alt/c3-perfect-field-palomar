/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license.
Adapted for C3PerfectField by Codex.

The Fitting and split-injection arguments follow the Tau Ceti contributors'
`TauCeti/RingTheory/KrullSchmidt/Indecomposable.lean` at commit
83769e442d55cda9d85b3927a93b286831c595ff. This module instead proves the
categorical-to-internal decomposition bridge directly with Mathlib's product
isomorphism. It imports no unchecked Tau Ceti declarations.
-/
module

public import C3PerfectField.Radicals
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Projection

/-! Fitting's lemma and manuscript Lemma `lem:noniso` for the actual modules. -/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v

section Modules

variable {A : Type*} [Ring A] {X Y : ModuleCat A}

/-- Convert an internal direct-sum decomposition into the categorical
decomposition occurring in the definition of indecomposable. -/
theorem eq_bot_or_eq_bot_of_indecomposable (hX : Indecomposable X)
    {N P : Submodule A X} (hNP : IsCompl N P) : N = ⊥ ∨ P = ⊥ := by
  let e : X ≅ ModuleCat.of A N ⊞ ModuleCat.of A P :=
    (N.prodEquivOfIsCompl P hNP).symm.toModuleIso ≪≫
      (ModuleCat.biprodIsoProd (ModuleCat.of A N) (ModuleCat.of A P)).symm
  rcases hX.2 (ModuleCat.of A N) (ModuleCat.of A P) e with hN | hP
  · exact Or.inl (Submodule.subsingleton_iff_eq_bot.mp
      (ModuleCat.isZero_iff_subsingleton.mp hN))
  · exact Or.inr (Submodule.subsingleton_iff_eq_bot.mp
      (ModuleCat.isZero_iff_subsingleton.mp hP))

theorem moduleEnd_isUnit_of_bijective (f : Module.End A X) (hf : Function.Bijective f) :
    IsUnit f := by
  let e := LinearEquiv.ofBijective f hf
  refine ⟨⟨f, e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
  · ext x
    exact e.apply_symm_apply x
  · ext x
    exact e.symm_apply_apply x

/-- Fitting's decomposition collapses to the kernel or the range for an
indecomposable module. The exponent used here is strictly positive. -/
theorem indecomposable_end_isNilpotent_or_isUnit
    [IsNoetherian A X] [IsArtinian A X] (hX : Indecomposable X)
    (f : Module.End A X) : IsNilpotent f ∨ IsUnit f := by
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
  have hcompl := hn (n + 1) (Nat.le_succ n)
  rcases eq_bot_or_eq_bot_of_indecomposable hX hcompl with hker | hrange
  · right
    have hpow : IsUnit (f ^ (n + 1)) :=
      moduleEnd_isUnit_of_bijective _ ⟨LinearMap.ker_eq_bot.mp hker,
        LinearMap.range_eq_top.mp (by simpa [hker] using hcompl.sup_eq_top)⟩
    exact (isUnit_pow_succ_iff (n := n)).mp hpow
  · exact Or.inl ⟨n + 1, LinearMap.range_eq_bot.mp hrange⟩

/-- An invertible composite through a nonzero indecomposable target forces
the first map to be an isomorphism. -/
theorem isIso_of_isIso_comp_of_indecomposable
    (hX : ¬IsZero X) (hY : Indecomposable Y)
    (f : X ⟶ Y) (g : Y ⟶ X) [IsIso (f ≫ g)] : IsIso f := by
  have : Nontrivial X := not_subsingleton_iff_nontrivial.mp
    (fun h => hX (ModuleCat.isZero_iff_subsingleton.mpr h))
  let e := (asIso (f ≫ g)).toLinearEquiv
  have hinj : Function.Injective f.hom :=
    Function.Injective.of_comp (f := g.hom) (g := f.hom) e.injective
  let p := f.hom.rangeRestrict ∘ₗ e.symm.toLinearMap ∘ₗ g.hom
  have hcompl : IsCompl f.hom.range p.ker := LinearMap.isCompl_of_proj (f := p) (by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    exact congrArg f.hom (e.symm_apply_apply x))
  have hker := (eq_bot_or_eq_bot_of_indecomposable hY hcompl).resolve_left
    (fun hf => LinearMap.ne_zero_of_injective hinj (LinearMap.range_eq_bot.mp hf))
  have hsurj : Function.Surjective f.hom :=
    LinearMap.range_eq_top.mp (by simpa [hker] using hcompl.sup_eq_top)
  exact (LinearEquiv.ofBijective f.hom ⟨hinj, hsurj⟩).toModuleIso.isIso_hom

end Modules

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Finite dimensionality over the base field is sufficient for Fitting's
lemma over `A`; no extra finiteness premise is introduced. -/
theorem isLocalRing_end_of_finite_indecomposable
    (X : IndecomposableModule k A) : IsLocalRing (End X.obj) := by
  let : Module.Finite k X.obj := X.val.property
  let : IsNoetherian A X.obj :=
    isNoetherian_of_tower k (inferInstance : IsNoetherian k X.obj)
  let : IsArtinian A X.obj :=
    isArtinian_of_tower k (inferInstance : IsArtinian k X.obj)
  have : Nontrivial X.obj := not_subsingleton_iff_nontrivial.mp
    (fun h => X.property.1 (ModuleCat.isZero_iff_subsingleton.mpr h))
  have : IsLocalRing (Module.End A X.obj) :=
    IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f =>
      (indecomposable_end_isNilpotent_or_isUnit X.property f).symm.imp id
        IsNilpotent.isUnit_one_sub
  exact X.obj.endRingEquiv.symm.isLocalRing

/-- Manuscript Lemma `lem:noniso`, with no local-ring premise: that premise
is proved above for every finite-dimensional indecomposable. -/
theorem isRadical_iff_not_isIso {X Y : IndecomposableModule k A} (f : X.obj ⟶ Y.obj) :
    IsRadical A f ↔ ¬IsIso f := by
  constructor
  · exact fun h => h.not_isIso X.property.1
  · intro hf g
    let := isLocalRing_end_of_finite_indecomposable X
    have hnon : ¬IsUnit (End.of (f ≫ g)) := by
      intro h
      let := (isUnit_iff_isIso _).mp h
      exact hf (isIso_of_isIso_comp_of_indecomposable X.property.1 Y.property f g)
    exact (isUnit_iff_isIso _).mp
      (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (End.of (f ≫ g)) hnon)

end C3PerfectField
