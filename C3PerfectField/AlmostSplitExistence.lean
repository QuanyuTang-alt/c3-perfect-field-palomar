module

public import C3PerfectField.TransposeModules
public import C3PerfectField.AlmostSplitPredecessors
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
Almost split existence, identified with the manuscript's chosen `D Tr`.
The imported Tau Ceti modules are included as adapted source, with their
copyright notices retained. `verification/vendor-tauceti.json` records the
verified upstream revision and distinguishes upstream, initial adaptation and
current release hashes; `verification/module-origins.json` covers all local
modules. The final theorem's proof dependency closure is axiom-audited, not
a claim that every declaration of the upstream repository was reviewed.
The cover predicate in that library uses superfluous kernels. The bridge
below derives that property from the manuscript's endomorphism minimality.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

instance finite_algebraModule (M : FiniteModule k A) : Module.Finite A M.val := by
  let : Module.Finite k M.val := M.property
  exact Module.Finite.of_restrictScalars_finite k A M.val

theorem tauCeti_isProjectiveCover {P X : FiniteModule k A} (p : P.val ⟶ X.val)
    (hp : IsProjectiveCover (k := k) p) : TauCeti.IsProjectiveCover p.hom := by
  let := hp.1
  let : Module.Projective A P.val := inferInstance
  have hsurj := (ModuleCat.epi_iff_surjective p).mp hp.2.1
  apply (TauCeti.isProjectiveCover_iff_forall_surjective hsurj).mpr
  intro Q _ _ h hh
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (p.hom.comp h) p.hom hh
  let a : P.val ⟶ P.val := ModuleCat.ofHom (h.comp s)
  have hap : a ≫ p = p := by
    apply ModuleCat.hom_ext
    exact (LinearMap.comp_assoc _ _ _).symm.trans hs
  let := hp.2.2 a hap
  have ha := (ModuleCat.epi_iff_surjective a).mp inferInstance
  intro x
  obtain ⟨y, hy⟩ := ha x
  exact ⟨s y, hy⟩

namespace MinimalProjectivePresentation

variable {X : FiniteModule k A} (T : MinimalProjectivePresentation X)

/-- The existing chosen presentation, packaged for the checked library. -/
def tauCetiPresentation : TauCeti.FiniteProjectivePresentation X.val := by
  let : Module.Finite k T.P₀.val := T.P₀.property
  let : Module.Finite k T.P₁.val := T.P₁.property
  let : Module.Finite A T.P₀.val := Module.Finite.of_restrictScalars_finite k A _
  let : Module.Finite A T.P₁.val := Module.Finite.of_restrictScalars_finite k A _
  let := T.cover₀.1
  let := T.cover₁.1
  exact {
    P₀ := T.P₀.val
    P₁ := T.P₁.val
    p := T.differential.hom
    π := T.p₀.hom
    exact := LinearMap.exact_iff.mpr T.range_differential.symm
    surjective := (ModuleCat.epi_iff_surjective T.p₀).mp T.cover₀.2.1
  }

theorem tauCetiPresentation_isMinimal :
    TauCeti.IsMinimalProjectivePresentation T.tauCetiPresentation.p
      T.tauCetiPresentation.π := by
  have h₀ := tauCeti_isProjectiveCover T.p₀ T.cover₀
  have h₁ := tauCeti_isProjectiveCover T.p₁ T.cover₁
  simpa only [tauCetiPresentation, differential, moduleKernelInclusion,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      h₀.isMinimalProjectivePresentation h₁

/-- The two transposes use the same right-module quotient and scalar
action. This includes the explicit bundled/native scalar comparison. -/
def tauCetiTransposeCarrierEquiv :
    TauCeti.AuslanderReitenTranspose T.differential.hom ≃ₗ[Aᵐᵒᵖ]
      T.transposeCarrier :=
  TauCeti.AuslanderReitenTranspose.quotientEquiv T.differential.hom
    (LinearMap.range T.transposeMap) (LinearEquiv.refl Aᵐᵒᵖ _) (by
      rw [LinearEquiv.refl_toLinearMap, Submodule.map_id]
      rfl)

def tauCetiTransposeScalarEquiv :
    T.transposeModule ≃ₗ[k] TauCeti.AuslanderReitenTranspose T.differential.hom :=
  T.transposeScalarEquiv.trans
    (T.tauCetiTransposeCarrierEquiv.restrictScalars k).symm

theorem tauCetiTransposeScalarEquiv_symm_smul (a : Aᵐᵒᵖ)
    (ψ : TauCeti.AuslanderReitenTranspose T.differential.hom) :
    T.tauCetiTransposeScalarEquiv.symm (a • ψ) =
      a • T.tauCetiTransposeScalarEquiv.symm ψ := by
  change T.transposeScalarEquiv.symm (T.tauCetiTransposeCarrierEquiv (a • ψ)) = _
  rw [T.tauCetiTransposeCarrierEquiv.map_smul]
  rfl

noncomputable def tauCetiDualTransposeScalarEquiv [FiniteDimensional k A] :
    T.dualTransposeModule.val ≃ₗ[k]
      TauCeti.AuslanderReitenTranslate k T.differential.hom :=
  (rightDualScalarEquiv T.finiteTransposeModule.val).trans
    T.tauCetiTransposeScalarEquiv.symm.dualMap

theorem tauCetiDualTransposeScalarEquiv_apply [FiniteDimensional k A]
    (φ : T.dualTransposeModule.val)
    (ψ : TauCeti.AuslanderReitenTranspose T.differential.hom) :
    T.tauCetiDualTransposeScalarEquiv φ ψ =
      rightDualScalarEquiv T.finiteTransposeModule.val φ
        (T.tauCetiTransposeScalarEquiv.symm ψ) := rfl

/-- The comparison respects the actual left `A`-action, so the almost
split kernel is the manuscript's `D Tr`, not just a space of equal dimension. -/
noncomputable def tauCetiDualTransposeModuleEquiv [FiniteDimensional k A] :
    T.dualTransposeModule.val ≃ₗ[A]
      ModuleCat.of A (TauCeti.AuslanderReitenTranslate k T.differential.hom) where
  toEquiv := T.tauCetiDualTransposeScalarEquiv.toEquiv
  map_add' := T.tauCetiDualTransposeScalarEquiv.map_add
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro ψ
    change T.tauCetiDualTransposeScalarEquiv (a • φ) ψ =
      (a • T.tauCetiDualTransposeScalarEquiv φ) ψ
    rw [TauCeti.AuslanderReitenTranslate.smul_apply,
      T.tauCetiDualTransposeScalarEquiv_apply,
      T.tauCetiDualTransposeScalarEquiv_apply,
      T.tauCetiTransposeScalarEquiv_symm_smul]
    rfl

noncomputable def arTranslateIsoDualTranspose [FiniteDimensional k A] :
    ModuleCat.arTranslate k X.val ≅ T.dualTransposeModule.val := by
  let : Module.Finite k X.val := X.property
  let : Module.Finite A X.val := Module.Finite.of_restrictScalars_finite k A _
  let e := Classical.choice (ModuleCat.nonempty_iso_arTranslate k X.val T.tauCetiPresentation
    T.tauCetiPresentation_isMinimal)
  exact e ≪≫ T.tauCetiDualTransposeModuleEquiv.toModuleIso.symm

end MinimalProjectivePresentation

theorem isRightAlmostSplit_of_tauCeti {E X : FiniteModule k A}
    (q : E.val ⟶ X.val) (hq : TauCeti.IsRightAlmostSplit q) :
    IsRightAlmostSplit (k := k) q := by
  refine ⟨hq.not_isSplitEpi, ?_⟩
  intro Y f hf
  obtain ⟨a, ha⟩ := hq.factors Y.val f hf
  exact ⟨a, ha.symm⟩

/-- Unconditional almost split existence for each nonprojective
indecomposable, with kernel the dual transpose of any chosen minimal
projective presentation in the manuscript's sense. -/
theorem exists_rightAlmostSplit_dualTranspose [FiniteDimensional k A]
    (X : IndecomposableModule k A) (hX : ¬Projective X.obj)
    (T : MinimalProjectivePresentation X.val) :
    ∃ (E : FiniteModule k A) (i : T.dualTransposeModule.val ⟶ E.val)
      (q : E.val ⟶ X.obj) (h : i ≫ q = 0),
      (ShortComplex.mk i q h).ShortExact ∧ IsRightAlmostSplit (k := k) q := by
  let : Module.Finite k X.obj := X.val.property
  let : Module.Finite A X.obj := Module.Finite.of_restrictScalars_finite k A _
  obtain ⟨E, i, q, h, hE, hS⟩ :=
    ModuleCat.exists_isAlmostSplit_arTranslate k X.obj X.property hX
  let : Module.Finite A E := hE
  let F : FiniteModule k A := ⟨E, Module.Finite.trans A E⟩
  let e := T.arTranslateIsoDualTranspose
  have hz : (e.inv ≫ i) ≫ q = 0 := by simp [Category.assoc, h]
  refine ⟨F, e.inv ≫ i, q, hz, ?_,
    isRightAlmostSplit_of_tauCeti (E := F) (X := X.val) q hS.isRightAlmostSplit_g⟩
  exact ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk i q h)
    (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)) hS.shortExact

/-- Rank-nullity for the actual short exact sequence, using its module
maps restricted to the base field. -/
theorem finrank_middle_of_shortExact {K E X : FiniteModule k A}
    (i : K.val ⟶ E.val) (q : E.val ⟶ X.val) (h : i ≫ q = 0)
    (hS : (ShortComplex.mk i q h).ShortExact) :
    Module.finrank k E.val = Module.finrank k X.val + Module.finrank k K.val := by
  let : Module.Finite k K.val := K.property
  let : Module.Finite k E.val := E.property
  let : Module.Finite k X.val := X.property
  let f := i.hom.restrictScalars k
  let g := q.hom.restrictScalars k
  have hk : LinearMap.ker g = LinearMap.range f := by
    ext x
    constructor
    · intro hx
      exact (ShortComplex.moduleCat_exact_iff _).mp hS.exact x hx
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) y
  have hr := g.finrank_range_add_finrank_ker
  have hg : Function.Surjective g := hS.moduleCat_surjective_g
  have hf : Function.Injective f := hS.moduleCat_injective_f
  rw [hk, LinearMap.range_eq_top.mpr hg,
    finrank_top, LinearMap.finrank_range_of_inj hf] at hr
  exact hr.symm

/-- The manuscript's source estimate is now derived from actual existence,
the identified `D Tr`, exactness, and the proved transpose bound. -/
theorem exists_rightAlmostSplit_source_bound_nonprojective [FiniteDimensional k A]
    (X : IndecomposableModule k A) (hX : ¬Projective X.obj) :
    ∃ (E : FiniteModule k A) (q : E.val ⟶ X.obj),
      IsRightAlmostSplit (k := k) q ∧
        Module.finrank k E.val ≤
          (1 + (Module.finrank k A) ^ 2) * Module.finrank k X.obj := by
  obtain ⟨T⟩ := exists_minimalProjectivePresentation X.val
  obtain ⟨E, i, q, h, hs, hq⟩ := exists_rightAlmostSplit_dualTranspose X hX T
  refine ⟨E, q, hq, ?_⟩
  rw [finrank_middle_of_shortExact i q h hs, Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_left T.finrank_dualTransposeModule_le _

end C3PerfectField
