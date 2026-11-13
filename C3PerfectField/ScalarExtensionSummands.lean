module

public import C3PerfectField.ScalarExtensionRadicals
public import C3PerfectField.FiniteDecomposition

/-!
Manuscript `lem:disjoint` and `cor:infinite-extension`.
Nonisomorphic indecomposables have only radical maps after extension,
so a common retract must be zero. Choosing an indecomposable summand
then gives an injection on the actual isomorphism classes.
An algebraic closure is taken in the universe of the base field.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct

universe u v

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- All maps between extensions of distinct indecomposables are radical. -/
theorem isRadical_scalarExtension_of_noniso
    (X Y : IndecomposableModule k A) (hXY : ¬Nonempty (X.obj ≅ Y.obj))
    (f : scalarExtensionObject (k := k) (K := K) X.obj ⟶
      scalarExtensionObject (k := k) (K := K) Y.obj) :
    IsRadical (K ⊗[k] A) f := by
  let : Module.Finite k X.obj := X.val.property
  let : Module.Finite k Y.obj := Y.val.property
  have hr : radicalSubmodule (k := k) X.obj Y.obj = ⊤ := by
    apply eq_top_iff.mpr
    intro g _
    exact (isRadical_iff_not_isIso g).mpr (fun hg => hXY ⟨@asIso _ _ _ _ g hg⟩)
  obtain ⟨z, rfl⟩ := (moduleHomScalarExtensionEquiv (k := k) (K := K) X.obj Y.obj).surjective f
  apply (isRadical_moduleHomScalarExtensionEquiv_iff X.obj Y.obj z).mpr
  rw [hr, Submodule.baseChange_top]
  trivial

/-- Manuscript `lem:disjoint`: any common direct summand is zero.
The retracts use the actual scalar-extended objects. -/
theorem scalarExtension_common_retract_isZero
    (X Y : IndecomposableModule k A) (hXY : ¬Nonempty (X.obj ≅ Y.obj))
    (Z : ModuleCat.{max u v} (K ⊗[k] A))
    (hX : Retract Z (scalarExtensionObject (k := k) (K := K) X.obj))
    (hY : Retract Z (scalarExtensionObject (k := k) (K := K) Y.obj)) :
    IsZero Z := by
  have hf := isRadical_scalarExtension_of_noniso X Y hXY (hX.r ≫ hY.i)
  have hid : IsRadical (K ⊗[k] A) (𝟙 Z) := by
    have h := (hf.precomp hX.i).postcomp hY.r
    simpa only [← Category.assoc, hX.retract, Category.id_comp, hY.retract] using h
  exact isRadical_id_iff_isZero.mp hid

/-- A nonzero finite module has a nonzero indecomposable direct summand. -/
theorem exists_indecomposable_summand_of_not_isZero
    {F : Type*} {B : Type*} [Field F] [Ring B] [Algebra F B]
    (W : FiniteModule F B) (hW : ¬IsZero W.val) :
    ∃ Z : IndecomposableModule F B, IsIndecomposableSummand Z W := by
  classical
  obtain ⟨n, P, ⟨e⟩⟩ := exists_indecomposable_biproduct W
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hz : IsZero (⨁ fun i => (P i).obj) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      exact (ModuleCat.biproductIsoPi (fun i => (P i).obj)).toLinearEquiv.injective.subsingleton
    exact hW (hz.of_iso e)
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  exact ⟨P i, (isIndecomposableSummand_iff_component_iso (P i) W P e).mpr
    ⟨i, ⟨Iso.refl _⟩⟩⟩

omit [Module.Finite k A] [PerfectField k] [IsAlgClosure k K] in
/-- Faithful tensor extension preserves nonzero finite modules. -/
theorem not_isZero_scalarExtension_indecomposable (X : IndecomposableModule k A) :
    ¬IsZero (scalarExtensionFiniteModule (L := K) X.val).val := by
  intro hzero
  have hs : Subsingleton (K ⊗[k] X.obj) :=
    (ModuleCat.isZero_iff_subsingleton.mp hzero)
  have hX : Subsingleton X.obj := scalarExtension_subsingleton_iff.mp hs
  exact X.property.1 (ModuleCat.isZero_iff_subsingleton.mpr hX)

omit [Module.Finite k A] [PerfectField k] [IsAlgClosure k K] in
/-- Every extended indecomposable has at least one indecomposable summand. -/
theorem exists_scalarExtension_indecomposable_summand (X : IndecomposableModule k A) :
    ∃ Z : IndecomposableModule K (K ⊗[k] A),
      IsIndecomposableSummand Z (scalarExtensionFiniteModule (L := K) X.val) :=
  exists_indecomposable_summand_of_not_isZero _
    (not_isZero_scalarExtension_indecomposable X)

/-- A chosen indecomposable summand for each actual base-field isomorphism class. -/
def scalarExtensionChosenSummand (x : ARVertex k A) :
    IndecomposableModule K (K ⊗[k] A) :=
  (exists_scalarExtension_indecomposable_summand (K := K) x.out).choose

omit [Module.Finite k A] [PerfectField k] [IsAlgClosure k K] in
theorem scalarExtensionChosenSummand_isSummand (x : ARVertex k A) :
    IsIndecomposableSummand (scalarExtensionChosenSummand (K := K) x)
      (scalarExtensionFiniteModule (L := K) x.out.val) :=
  (exists_scalarExtension_indecomposable_summand (K := K) x.out).choose_spec

/-- The chosen summands define a map on actual AR vertex sets. -/
def scalarExtensionSummandVertex (x : ARVertex k A) : ARVertex K (K ⊗[k] A) :=
  Quotient.mk _ (scalarExtensionChosenSummand (K := K) x)

/-- Distinct base-field isomorphism classes cannot acquire a common
indecomposable summand class. No Galois orbit premise is needed here. -/
theorem scalarExtensionSummandVertex_injective :
    Function.Injective (scalarExtensionSummandVertex (k := k) (K := K) (A := A)) := by
  intro x y hxy
  by_contra hne
  have hnon : ¬Nonempty (x.out.obj ≅ y.out.obj) := by
    intro h
    have hm : (Quotient.mk _ x.out : ARVertex k A) = Quotient.mk _ y.out :=
      Quotient.sound h
    exact hne (by simpa only [Quotient.out_eq] using hm)
  let Z := scalarExtensionChosenSummand (K := K) x
  let W := scalarExtensionChosenSummand (K := K) y
  have hZW : Nonempty (Z.obj ≅ W.obj) := Quotient.exact hxy
  obtain ⟨e⟩ := hZW
  obtain ⟨iX, pX, hiX⟩ := scalarExtensionChosenSummand_isSummand (K := K) x
  obtain ⟨iY, pY, hiY⟩ := scalarExtensionChosenSummand_isSummand (K := K) y
  have hx : Retract Z.obj (scalarExtensionObject (k := k) (K := K) x.out.obj) :=
    ⟨iX, pX, hiX⟩
  change W.obj ⟶ scalarExtensionObject (k := k) (K := K) y.out.obj at iY
  change scalarExtensionObject (k := k) (K := K) y.out.obj ⟶ W.obj at pY
  change iY ≫ pY = 𝟙 W.obj at hiY
  have hy : Retract Z.obj (scalarExtensionObject (k := k) (K := K) y.out.obj) :=
    ⟨e.hom ≫ iY, pY ≫ e.inv, by
      rw [Category.assoc e.hom iY (pY ≫ e.inv), ← Category.assoc iY pY e.inv,
        hiY, Category.id_comp, e.hom_inv_id]⟩
  exact Z.property.1 (scalarExtension_common_retract_isZero x.out y.out hnon Z.obj hx hy)

/-- Manuscript `cor:infinite-extension`, for the actual indecomposable
isomorphism classes used in the main theorem. -/
theorem infiniteRepresentationType_scalarExtension
    (hA : InfiniteRepresentationType k A) :
    InfiniteRepresentationType K (K ⊗[k] A) := by
  let : Infinite (ARVertex k A) := hA
  exact Infinite.of_injective (scalarExtensionSummandVertex (k := k) (K := K) (A := A))
    scalarExtensionSummandVertex_injective

end

end C3PerfectField
