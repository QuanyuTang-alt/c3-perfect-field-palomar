module

public import C3PerfectField.FiniteModelModules
public import C3PerfectField.ScalarExtensionSummands

/-!
Manuscript `lem:summand-descent`, second assertion. An indecomposable
extended module is a retract of the extension of one indecomposable base
module. The finite-sum matching argument works even when the scalar
extensions of the base indecomposables are themselves decomposable.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- A finite sum of factorizations of an indecomposable identity has a
unit component. This does not require indecomposable intermediate objects. -/
theorem exists_retract_component_of_identity_sum
    (X : IndecomposableModule k A) {η : Type*} [Fintype η]
    (W : η → ModuleCat.{max u v} A)
    (a : ∀ i, X.obj ⟶ W i) (b : ∀ i, W i ⟶ X.obj)
    (hab : ∑ i, a i ≫ b i = 𝟙 X.obj) :
    ∃ i, Nonempty (Retract X.obj (W i)) := by
  classical
  have hunit : ∃ i, IsIso (a i ≫ b i) := by
    by_contra h
    push Not at h
    have hr : IsRadical A (∑ i, a i ≫ b i) :=
      isRadical_sum Finset.univ _ fun i _ =>
        (isRadical_iff_not_isIso (X := X) (Y := X) _).mpr (h i)
    exact X.property.1 (isRadical_id_iff_isZero.mp (hab ▸ hr))
  obtain ⟨i, hi⟩ := hunit
  let := hi
  let e := asIso (a i ≫ b i)
  exact ⟨i, ⟨⟨a i, b i ≫ e.inv, by
    rw [← Category.assoc]
    exact e.hom_inv_id⟩⟩⟩

variable {K : Type u} [Field K] [Algebra k K]

/-- An indecomposable retract of an extended finite sum is already a retract
of the extension of one of its base-field indecomposable components. -/
theorem exists_scalarExtension_retract_component
    (N : IndecomposableModule K (K ⊗[k] A)) (W : FiniteModule k A)
    (hN : Retract N.obj (scalarExtensionFiniteModule (L := K) W).val) :
    ∃ X : IndecomposableModule k A,
      IsIndecomposableSummand N (scalarExtensionFiniteModule (L := K) X.val) := by
  classical
  obtain ⟨n, P, ⟨e⟩⟩ := exists_indecomposable_biproduct W
  let F := scalarExtensionFunctor (k := k) (K := K) (A := A)
  let a (i : Fin n) := hN.i ≫ F.map (e.hom ≫ biproduct.π (fun j => (P j).obj) i)
  let b (i : Fin n) := F.map (biproduct.ι (fun j => (P j).obj) i ≫ e.inv) ≫ hN.r
  have he : ∑ i, (e.hom ≫ biproduct.π (fun j => (P j).obj) i) ≫
      (biproduct.ι (fun j => (P j).obj) i ≫ e.inv) = 𝟙 W.val := by
    calc
      _ = e.hom ≫ (∑ i, biproduct.π (fun j => (P j).obj) i ≫
          biproduct.ι (fun j => (P j).obj) i) ≫ e.inv := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 W.val := by simp
  have hab : ∑ i, a i ≫ b i = 𝟙 N.obj := by
    calc
      ∑ i, a i ≫ b i =
          hN.i ≫ F.map (∑ i, (e.hom ≫ biproduct.π (fun j => (P j).obj) i) ≫
            (biproduct.ι (fun j => (P j).obj) i ≫ e.inv)) ≫ hN.r := by
        simp only [a, b, F.map_sum, F.map_comp, Preadditive.comp_sum,
          Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 N.obj := by
        simp only [he, F.map_id]
        exact hN.retract
  obtain ⟨i, ⟨r⟩⟩ := exists_retract_component_of_identity_sum N
    (fun i => F.obj (P i).obj) a b hab
  exact ⟨P i, r.i, r.r, r.retract⟩

variable [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- Manuscript `lem:summand-descent` for indecomposables, with the actual
isomorphism-class representatives and scalar-extended module objects. -/
theorem exists_indecomposable_scalarExtension_summand
    (N : IndecomposableModule K (K ⊗[k] A)) :
    ∃ X : IndecomposableModule k A,
      IsIndecomposableSummand N (scalarExtensionFiniteModule (L := K) X.val) := by
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  obtain ⟨W, ⟨r⟩⟩ := exists_scalarExtension_retract N.val
  exact exists_scalarExtension_retract_component N W r

end

end C3PerfectField
