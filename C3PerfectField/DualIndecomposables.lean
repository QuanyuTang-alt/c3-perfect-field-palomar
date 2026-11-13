module

public import C3PerfectField.DualMorphisms
public import C3PerfectField.ARDimension

/-!
Field duality preserves nonzero finite indecomposable modules. The proof
uses actual split morphisms and double-dual evaluation, rather than assuming
an equivalence of representation categories.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

theorem finrank_pos_of_not_isZero (M : FiniteModule k A) (hM : ¬IsZero M.val) :
    0 < Module.finrank k M.val := by
  let : Module.Finite k M.val := M.property
  let : Nontrivial M.val := not_subsingleton_iff_nontrivial.mp
    (fun h => hM (ModuleCat.isZero_iff_subsingleton.mpr h))
  exact Module.finrank_pos

theorem not_isZero_of_finrank_pos (M : FiniteModule k A)
    (hM : 0 < Module.finrank k M.val) : ¬IsZero M.val := by
  intro h
  let : Subsingleton M.val := ModuleCat.isZero_iff_subsingleton.mp h
  exact (Nat.ne_of_gt hM) Module.finrank_zero_of_subsingleton

theorem not_isZero_leftDualModule (M : FiniteModule k A) (hM : ¬IsZero M.val) :
    ¬IsZero (finiteLeftDualModule M).val := by
  apply not_isZero_of_finrank_pos
  simpa only [finiteLeftDualModule, finrank_leftDualModule] using
    finrank_pos_of_not_isZero M hM

theorem not_isZero_rightDualModule (M : FiniteModule k Aᵐᵒᵖ) (hM : ¬IsZero M.val) :
    ¬IsZero (finiteRightDualModule M).val := by
  apply not_isZero_of_finrank_pos
  simpa only [finiteRightDualModule, finrank_rightDualModule] using
    finrank_pos_of_not_isZero M hM

/-- A nonzero finite module is indecomposable if each of its nonzero
retracts has the same dimension as the module. -/
theorem indecomposable_of_retract_dimension (M : FiniteModule k A)
    (hM : ¬IsZero M.val)
    (h : ∀ (U : FiniteModule k A), ¬IsZero U.val →
      ∀ (i : U.val ⟶ M.val) (r : M.val ⟶ U.val), i ≫ r = 𝟙 U.val →
        Module.finrank k U.val = Module.finrank k M.val) :
    Indecomposable M.val := by
  by_contra hdec
  obtain ⟨U, V, e, hU, hV⟩ := exists_smaller_biprod M hM hdec
  let : Module.Finite k U.val := U.property
  let : Module.Finite k V.val := V.property
  have hsum : Module.finrank k M.val = Module.finrank k U.val + Module.finrank k V.val := by
    rw [← Module.finrank_prod]
    exact ((e ≪≫ ModuleCat.biprodIsoProd U.val V.val).toLinearEquiv.restrictScalars k).finrank_eq
  have hUnz : ¬IsZero U.val := not_isZero_of_finrank_pos U (by omega)
  have hdim := h U hUnz (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp)
  omega

theorem indecomposable_leftDualModule (X : IndecomposableModule k A) :
    Indecomposable (finiteLeftDualModule X.val).val := by
  apply indecomposable_of_retract_dimension _ (not_isZero_leftDualModule X.val X.property.1)
  intro U hU i r hir
  let j : (finiteRightDualModule U).val ⟶ X.obj :=
    rightDualMap r ≫ (doubleDualModuleIso X.val).inv
  let t : X.obj ⟶ (finiteRightDualModule U).val :=
    (doubleDualModuleIso X.val).hom ≫ rightDualMap i
  have hjt : j ≫ t = 𝟙 (finiteRightDualModule U).val := by
    simp only [j, t, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← rightDualMap_comp, hir, rightDualMap_id]
    rfl
  let : IsIso (j ≫ t) := by rw [hjt]; infer_instance
  let : IsIso j := isIso_of_isIso_comp_of_indecomposable
    (not_isZero_rightDualModule U hU) X.property j t
  have hd := finrank_eq_of_module_iso (k := k) (asIso j)
  simpa only [finiteRightDualModule, finiteLeftDualModule, finrank_rightDualModule,
    finrank_leftDualModule] using hd

theorem indecomposable_rightDualModule (X : IndecomposableModule k Aᵐᵒᵖ) :
    Indecomposable (finiteRightDualModule X.val).val := by
  apply indecomposable_of_retract_dimension _ (not_isZero_rightDualModule X.val X.property.1)
  intro U hU i r hir
  let j : (finiteLeftDualModule U).val ⟶ X.obj :=
    leftDualMap r ≫ (rightDoubleDualModuleIso X.val).inv
  let t : X.obj ⟶ (finiteLeftDualModule U).val :=
    (rightDoubleDualModuleIso X.val).hom ≫ leftDualMap i
  have hjt : j ≫ t = 𝟙 (finiteLeftDualModule U).val := by
    simp only [j, t, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← leftDualMap_comp, hir, leftDualMap_id]
    rfl
  let : IsIso (j ≫ t) := by rw [hjt]; infer_instance
  let : IsIso j := isIso_of_isIso_comp_of_indecomposable
    (not_isZero_leftDualModule U hU) X.property j t
  have hd := finrank_eq_of_module_iso (k := k) (asIso j)
  simpa only [finiteLeftDualModule, finiteRightDualModule, finrank_leftDualModule,
    finrank_rightDualModule] using hd

def leftDualIndecomposable (X : IndecomposableModule k A) : IndecomposableModule k Aᵐᵒᵖ :=
  ⟨finiteLeftDualModule X.val, indecomposable_leftDualModule X⟩

def rightDualIndecomposable (X : IndecomposableModule k Aᵐᵒᵖ) : IndecomposableModule k A :=
  ⟨finiteRightDualModule X.val, indecomposable_rightDualModule X⟩

/-- Actual AR arrows reverse under field duality. -/
theorem hasARArrow_leftDual {X Y : IndecomposableModule k A}
    (h : HasARArrow k A X Y) :
    HasARArrow k Aᵐᵒᵖ (leftDualIndecomposable Y) (leftDualIndecomposable X) := by
  obtain ⟨f, hf⟩ := hasARArrow_iff_exists_irreducible.mp h
  exact hasARArrow_iff_exists_irreducible.mpr
    ⟨leftDualMap f, isIrreducible_leftDualMap f hf⟩

theorem hasARArrow_rightDual {X Y : IndecomposableModule k Aᵐᵒᵖ}
    (h : HasARArrow k Aᵐᵒᵖ X Y) :
    HasARArrow k A (rightDualIndecomposable Y) (rightDualIndecomposable X) := by
  obtain ⟨f, hf⟩ := hasARArrow_iff_exists_irreducible.mp h
  exact hasARArrow_iff_exists_irreducible.mpr
    ⟨rightDualMap f, isIrreducible_rightDualMap f hf⟩

end C3PerfectField
