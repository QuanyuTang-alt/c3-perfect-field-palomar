module

public import C3PerfectField.IndecomposableRadicals
public import C3PerfectField.RadicalBlocks
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-!
Manuscript Lemma `lem:irreducible`. The factorization condition quantifies
over all finite-dimensional intermediate modules. Binary decomposition and
dimension induction replace the use of full Krull--Schmidt uniqueness.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- The usual section/retraction definition of an irreducible morphism in
the finite-dimensional module category. -/
def IsIrreducibleMorphism {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y) : Prop :=
  ¬IsSplitMono f ∧ ¬IsSplitEpi f ∧
    ∀ (W : FiniteModule k A) (a : X ⟶ W.val) (b : W.val ⟶ Y),
      f = a ≫ b → IsSplitMono a ∨ IsSplitEpi b

theorem IsRadical.not_isSplitMono {X Y : ModuleCat.{max u v} A}
    {f : X ⟶ Y} (hf : IsRadical A f) (hX : ¬IsZero X) : ¬IsSplitMono f := by
  intro h
  let := h
  exact hX (hf.isZero_of_section (retraction f) (IsSplitMono.id f))

theorem IsRadical.not_isSplitEpi {X Y : ModuleCat.{max u v} A}
    {f : X ⟶ Y} (hf : IsRadical A f) (hY : ¬IsZero Y) : ¬IsSplitEpi f := by
  intro h
  let := h
  exact hY (hf.isZero_of_retraction (section_ f) (IsSplitEpi.id f))

/-- A summand of a finite-dimensional module is finite-dimensional. -/
theorem finite_of_isSplitMono {W : FiniteModule k A}
    {U : ModuleCat.{max u v} A} (i : U ⟶ W.val) [IsSplitMono i] :
    Module.Finite k U := by
  let : Module.Finite k W.val := W.property
  exact FiniteDimensional.of_injective (i.hom.restrictScalars k)
    ((ModuleCat.mono_iff_injective i).mp (inferInstance : Mono i))

/-- A nonzero decomposable finite module splits into two finite modules of
strictly smaller dimension. No decomposition theorem is assumed here. -/
theorem exists_smaller_biprod (W : FiniteModule k A) (hW : ¬IsZero W.val)
    (hdec : ¬Indecomposable W.val) :
    ∃ (U V : FiniteModule k A) (_e : W.val ≅ U.val ⊞ V.val),
      Module.finrank k U.val < Module.finrank k W.val ∧
      Module.finrank k V.val < Module.finrank k W.val := by
  classical
  have h : ¬∀ U V : ModuleCat.{max u v} A,
      (W.val ≅ U ⊞ V) → IsZero U ∨ IsZero V := fun hd => hdec ⟨hW, hd⟩
  push Not at h
  obtain ⟨U, V, e, hU, hV⟩ := h
  let iU : U ⟶ W.val := biprod.inl ≫ e.inv
  let iV : V ⟶ W.val := biprod.inr ≫ e.inv
  let : Module.Finite k U := finite_of_isSplitMono (W := W) iU
  let : Module.Finite k V := finite_of_isSplitMono (W := W) iV
  let : Module.Finite k W.val := W.property
  let : Nontrivial U := not_subsingleton_iff_nontrivial.mp
    (fun hs => hU (ModuleCat.isZero_iff_subsingleton.mpr hs))
  let : Nontrivial V := not_subsingleton_iff_nontrivial.mp
    (fun hs => hV (ModuleCat.isZero_iff_subsingleton.mpr hs))
  have hrank : Module.finrank k W.val =
      Module.finrank k U + Module.finrank k V := by
    rw [← Module.finrank_prod]
    exact ((e ≪≫ ModuleCat.biprodIsoProd U V).toLinearEquiv.restrictScalars k).finrank_eq
  have hupos := Module.finrank_pos (R := k) (M := U)
  have hvpos := Module.finrank_pos (R := k) (M := V)
  refine ⟨⟨U, inferInstance⟩, ⟨V, inferInstance⟩, e, ?_, ?_⟩
  · change Module.finrank k U < Module.finrank k W.val
    omega
  · change Module.finrank k V < Module.finrank k W.val
    omega

/-- Every composite of a nonsection and a nonretraction through a finite
module lies in the radical square, for indecomposable endpoints. -/
theorem radicalSquare_of_nonsplit_factorization
    {X Y : IndecomposableModule k A} (W : FiniteModule k A)
    (a : X.obj ⟶ W.val) (b : W.val ⟶ Y.obj)
    (ha : ¬IsSplitMono a) (hb : ¬IsSplitEpi b) :
    IsRadicalSquare k A (a ≫ b) := by
  classical
  generalize hn : Module.finrank k W.val = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    by_cases hzero : IsZero W.val
    · rw [hzero.eq_zero_of_tgt a, zero_comp]
      exact isRadicalSquare_zero
    by_cases hind : Indecomposable W.val
    · let Z : IndecomposableModule k A := ⟨W, hind⟩
      have harad : IsRadical A a :=
        (isRadical_iff_not_isIso (X := X) (Y := Z) a).mpr (by
          intro h
          let := h
          exact ha (inferInstance : IsSplitMono a))
      have hbrad : IsRadical A b :=
        (isRadical_iff_not_isIso (X := Z) (Y := Y) b).mpr (by
          intro h
          let := h
          exact hb (inferInstance : IsSplitEpi b))
      refine ⟨1, fun _ => W, fun _ => a, fun _ => b,
        fun _ => ⟨harad, hbrad⟩, ?_⟩
      simp
    obtain ⟨U, V, e, hU, hV⟩ := exists_smaller_biprod W hzero hind
    let aU : X.obj ⟶ U.val := a ≫ e.hom ≫ biprod.fst
    let aV : X.obj ⟶ V.val := a ≫ e.hom ≫ biprod.snd
    let bU : U.val ⟶ Y.obj := biprod.inl ≫ e.inv ≫ b
    let bV : V.val ⟶ Y.obj := biprod.inr ≫ e.inv ≫ b
    have haU : ¬IsSplitMono aU := by
      intro h
      let := h
      apply ha
      exact IsSplitMono.mk' ⟨e.hom ≫ biprod.fst ≫ retraction aU, by
        simpa only [aU, Category.assoc] using IsSplitMono.id aU⟩
    have haV : ¬IsSplitMono aV := by
      intro h
      let := h
      apply ha
      exact IsSplitMono.mk' ⟨e.hom ≫ biprod.snd ≫ retraction aV, by
        simpa only [aV, Category.assoc] using IsSplitMono.id aV⟩
    have hbU : ¬IsSplitEpi bU := by
      intro h
      let := h
      apply hb
      exact IsSplitEpi.mk' ⟨section_ bU ≫ biprod.inl ≫ e.inv, by
        simpa only [bU, Category.assoc] using IsSplitEpi.id bU⟩
    have hbV : ¬IsSplitEpi bV := by
      intro h
      let := h
      apply hb
      exact IsSplitEpi.mk' ⟨section_ bV ≫ biprod.inr ≫ e.inv, by
        simpa only [bV, Category.assoc] using IsSplitEpi.id bV⟩
    have hsU := ih (Module.finrank k U.val) (by omega) U aU bU haU hbU rfl
    have hsV := ih (Module.finrank k V.val) (by omega) V aV bV haV hbV rfl
    have hsum : a ≫ b = aU ≫ bU + aV ≫ bV := by
      calc
        a ≫ b = a ≫ e.hom ≫ (𝟙 (U.val ⊞ V.val)) ≫ e.inv ≫ b := by simp
        _ = _ := by
          rw [← biprod.total]
          simp only [aU, aV, bU, bV, Preadditive.comp_add, Preadditive.add_comp,
            Category.assoc]
    rw [hsum]
    exact hsU.add hsV

/-- A finite biproduct of finite-dimensional modules is finite-dimensional. -/
theorem finite_biproduct {n : ℕ} (W : Fin n → FiniteModule k A) :
    Module.Finite k (⨁ fun j => (W j).val : ModuleCat.{max u v} A) := by
  let : ∀ j, Module.Finite k (W j).val := fun j => (W j).property
  let e := ModuleCat.biproductIsoPi (fun j => (W j).val)
  exact FiniteDimensional.of_injective (e.hom.hom.restrictScalars k)
    e.toLinearEquiv.injective

/-- Combine any radical-square sum into one factorization through a finite
biproduct, with both combined factors radical. -/
theorem IsRadicalSquare.exists_radical_factorization
    {X Y : ModuleCat.{max u v} A} {f : X ⟶ Y} (hf : IsRadicalSquare k A f) :
    ∃ (W : FiniteModule k A) (a : X ⟶ W.val) (b : W.val ⟶ Y),
      IsRadical A a ∧ IsRadical A b ∧ f = a ≫ b := by
  classical
  obtain ⟨n, W, a, b, hab, hsum⟩ := hf
  let T : FiniteModule k A := ⟨⨁ (fun j => (W j).val), finite_biproduct W⟩
  refine ⟨T, biproduct.lift a, biproduct.desc b, ?_, ?_, ?_⟩
  · rw [biproduct.lift_eq]
    exact isRadical_sum Finset.univ _ fun j _ => (hab j).1.postcomp _
  · rw [biproduct.desc_eq]
    exact isRadical_sum Finset.univ _ fun j _ => (hab j).2.precomp _
  · rw [biproduct.lift_desc]
    exact hsum

/-- Manuscript Lemma `lem:irreducible`, with the usual nonsplit-factorization
definition on the left and the exact target radical-square definition on the
right. No representation-theoretic hypothesis is added. -/
theorem isIrreducibleMorphism_iff_radical_not_square
    {X Y : IndecomposableModule k A} (f : X.obj ⟶ Y.obj) :
    IsIrreducibleMorphism (k := k) f ↔
      IsRadical A f ∧ ¬IsRadicalSquare k A f := by
  constructor
  · intro hf
    have hrad : IsRadical A f := (isRadical_iff_not_isIso f).mpr (by
      intro h
      let := h
      exact hf.1 (inferInstance : IsSplitMono f))
    refine ⟨hrad, ?_⟩
    intro hsquare
    obtain ⟨W, a, b, ha, hb, hfac⟩ := hsquare.exists_radical_factorization
    rcases hf.2.2 W a b hfac with hs | hr
    · exact ha.not_isSplitMono X.property.1 hs
    · exact hb.not_isSplitEpi Y.property.1 hr
  · rintro ⟨hrad, hnot⟩
    refine ⟨hrad.not_isSplitMono X.property.1, hrad.not_isSplitEpi Y.property.1, ?_⟩
    intro W a b hfac
    by_contra h
    push Not at h
    exact hnot (hfac ▸ radicalSquare_of_nonsplit_factorization W a b h.1 h.2)

/-- Thus the arrow relation used by the main statement has the ordinary
irreducible-morphism interpretation on every pair of representatives. -/
theorem hasARArrow_iff_exists_irreducible {X Y : IndecomposableModule k A} :
    HasARArrow k A X Y ↔
      ∃ f : X.obj ⟶ Y.obj, IsIrreducibleMorphism (k := k) f := by
  exact exists_congr fun f => (isIrreducibleMorphism_iff_radical_not_square f).symm

end C3PerfectField
