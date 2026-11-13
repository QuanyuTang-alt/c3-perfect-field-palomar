module

public import C3PerfectField.ModuleDuality
public import C3PerfectField.IrreducibleMorphisms

/-!
Field duality reverses sections, retractions, and irreducible morphisms in
the actual finite-dimensional module categories. The factorization proof
uses every finite intermediate module on the opposite side.
-/

@[expose] public section

-- Permit definitional comparison through the bundled finite-module subtype.
set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

open CategoryTheory
open scoped ModuleCat

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

theorem leftDualMap_isSplitEpi_of_isSplitMono {M N : ModuleCat.{max u v} A}
    (f : M ⟶ N) [IsSplitMono f] : IsSplitEpi (leftDualMap (k := k) f) := by
  refine IsSplitEpi.mk' ⟨leftDualMap (retraction f), ?_⟩
  rw [← leftDualMap_comp, IsSplitMono.id, leftDualMap_id]

theorem leftDualMap_isSplitMono_of_isSplitEpi {M N : ModuleCat.{max u v} A}
    (f : M ⟶ N) [IsSplitEpi f] : IsSplitMono (leftDualMap (k := k) f) := by
  refine IsSplitMono.mk' ⟨leftDualMap (section_ f), ?_⟩
  rw [← leftDualMap_comp, IsSplitEpi.id, leftDualMap_id]

theorem rightDualMap_isSplitEpi_of_isSplitMono {M N : ModuleCat.{max u v} Aᵐᵒᵖ}
    (f : M ⟶ N) [IsSplitMono f] : IsSplitEpi (rightDualMap (k := k) f) := by
  refine IsSplitEpi.mk' ⟨rightDualMap (retraction f), ?_⟩
  rw [← rightDualMap_comp, IsSplitMono.id, rightDualMap_id]

theorem rightDualMap_isSplitMono_of_isSplitEpi {M N : ModuleCat.{max u v} Aᵐᵒᵖ}
    (f : M ⟶ N) [IsSplitEpi f] : IsSplitMono (rightDualMap (k := k) f) := by
  refine IsSplitMono.mk' ⟨rightDualMap (section_ f), ?_⟩
  rw [← rightDualMap_comp, IsSplitEpi.id, rightDualMap_id]

theorem doubleDual_conjugate {M N : FiniteModule k A} (f : M.val ⟶ N.val) :
    f = (doubleDualModuleIso M).hom ≫ rightDualMap (leftDualMap (k := k) f) ≫
      (doubleDualModuleIso N).inv := by
  rw [← Category.assoc, ← doubleDualModuleIso_naturality]
  simp

theorem rightDoubleDual_conjugate {M N : FiniteModule k Aᵐᵒᵖ} (f : M.val ⟶ N.val) :
    f = (rightDoubleDualModuleIso M).hom ≫ leftDualMap (rightDualMap (k := k) f) ≫
      (rightDoubleDualModuleIso N).inv := by
  rw [← Category.assoc, ← rightDoubleDualModuleIso_naturality]
  simp

theorem leftDualMap_isSplitEpi_iff {M N : FiniteModule k A} (f : M.val ⟶ N.val) :
    IsSplitEpi (leftDualMap (k := k) f) ↔ IsSplitMono f := by
  constructor
  · intro h
    let := h
    let := rightDualMap_isSplitMono_of_isSplitEpi (k := k) (leftDualMap (k := k) f)
    rw [doubleDual_conjugate f]
    infer_instance
  · intro h
    let := h
    exact leftDualMap_isSplitEpi_of_isSplitMono f

theorem leftDualMap_isSplitMono_iff {M N : FiniteModule k A} (f : M.val ⟶ N.val) :
    IsSplitMono (leftDualMap (k := k) f) ↔ IsSplitEpi f := by
  constructor
  · intro h
    let := h
    let := rightDualMap_isSplitEpi_of_isSplitMono (k := k) (leftDualMap (k := k) f)
    rw [doubleDual_conjugate f]
    infer_instance
  · intro h
    let := h
    exact leftDualMap_isSplitMono_of_isSplitEpi f

theorem rightDualMap_isSplitEpi_iff {M N : FiniteModule k Aᵐᵒᵖ} (f : M.val ⟶ N.val) :
    IsSplitEpi (rightDualMap (k := k) f) ↔ IsSplitMono f := by
  constructor
  · intro h
    let := h
    let := leftDualMap_isSplitMono_of_isSplitEpi (k := k) (rightDualMap (k := k) f)
    rw [rightDoubleDual_conjugate f]
    infer_instance
  · intro h
    let := h
    exact rightDualMap_isSplitEpi_of_isSplitMono f

theorem rightDualMap_isSplitMono_iff {M N : FiniteModule k Aᵐᵒᵖ} (f : M.val ⟶ N.val) :
    IsSplitMono (rightDualMap (k := k) f) ↔ IsSplitEpi f := by
  constructor
  · intro h
    let := h
    let := leftDualMap_isSplitEpi_of_isSplitMono (k := k) (rightDualMap (k := k) f)
    rw [rightDoubleDual_conjugate f]
    infer_instance
  · intro h
    let := h
    exact rightDualMap_isSplitMono_of_isSplitEpi f

/-- Dualizing an irreducible map quantifies over all finite right modules;
double-dual evaluation converts each of their factorizations back to one
in the original category. -/
theorem isIrreducible_leftDualMap {M N : FiniteModule k A} (f : M.val ⟶ N.val)
    (hf : IsIrreducibleMorphism (k := k) f) :
    IsIrreducibleMorphism (k := k) (leftDualMap (k := k) f) := by
  refine ⟨fun h => hf.2.1 ((leftDualMap_isSplitMono_iff f).mp h),
    fun h => hf.1 ((leftDualMap_isSplitEpi_iff f).mp h), ?_⟩
  intro W a b hfac
  let U := finiteRightDualModule W
  let c : M.val ⟶ U.val := (doubleDualModuleIso M).hom ≫ rightDualMap b
  let d : U.val ⟶ N.val := rightDualMap a ≫ (doubleDualModuleIso N).inv
  have hcd : f = c ≫ d := by
    rw [doubleDual_conjugate f, hfac, rightDualMap_comp]
    simp only [c, d, Category.assoc]
  rcases hf.2.2 U c d hcd with hc | hd
  · let := hc
    have hb : IsSplitMono (rightDualMap (k := k) b) := by
      have heq : (doubleDualModuleIso M).inv ≫ c = rightDualMap (k := k) b := by
        simp [c]
      rw [← heq]
      infer_instance
    exact Or.inr ((rightDualMap_isSplitMono_iff
      (M := W) (N := finiteLeftDualModule M) b).mp hb)
  · let := hd
    have ha : IsSplitEpi (rightDualMap (k := k) a) := by
      have heq : d ≫ (doubleDualModuleIso N).hom = rightDualMap (k := k) a := by
        simp [d, Category.assoc]
      rw [← heq]
      infer_instance
    exact Or.inl ((rightDualMap_isSplitEpi_iff
      (M := finiteLeftDualModule N) (N := W) a).mp ha)

theorem isIrreducible_rightDualMap {M N : FiniteModule k Aᵐᵒᵖ} (f : M.val ⟶ N.val)
    (hf : IsIrreducibleMorphism (k := k) f) :
    IsIrreducibleMorphism (k := k) (rightDualMap (k := k) f) := by
  refine ⟨fun h => hf.2.1 ((rightDualMap_isSplitMono_iff f).mp h),
    fun h => hf.1 ((rightDualMap_isSplitEpi_iff f).mp h), ?_⟩
  intro W a b hfac
  let U := finiteLeftDualModule W
  let c : M.val ⟶ U.val := (rightDoubleDualModuleIso M).hom ≫ leftDualMap b
  let d : U.val ⟶ N.val := leftDualMap a ≫ (rightDoubleDualModuleIso N).inv
  have hcd : f = c ≫ d := by
    rw [rightDoubleDual_conjugate f, hfac, leftDualMap_comp]
    simp only [c, d, Category.assoc]
  rcases hf.2.2 U c d hcd with hc | hd
  · let := hc
    have hb : IsSplitMono (leftDualMap (k := k) b) := by
      have heq : (rightDoubleDualModuleIso M).inv ≫ c = leftDualMap (k := k) b := by
        simp [c]
      rw [← heq]
      infer_instance
    exact Or.inr ((leftDualMap_isSplitMono_iff
      (M := W) (N := finiteRightDualModule M) b).mp hb)
  · let := hd
    have ha : IsSplitEpi (leftDualMap (k := k) a) := by
      have heq : d ≫ (rightDoubleDualModuleIso N).hom = leftDualMap (k := k) a := by
        simp [d, Category.assoc]
      rw [← heq]
      infer_instance
    exact Or.inl ((leftDualMap_isSplitEpi_iff
      (M := finiteRightDualModule N) (N := W) a).mp ha)

end C3PerfectField
