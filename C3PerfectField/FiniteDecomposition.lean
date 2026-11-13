module

public import C3PerfectField.IrreducibleMorphisms

/-!
The existence part of manuscript External Theorem `ext:ks`, proved by
dimension induction for the actual finite-dimensional module category.
This module does not claim Krull--Schmidt uniqueness.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Joining finite families of modules joins their biproducts. The proof
uses Mathlib's explicit dependent-product model of module biproducts. -/
noncomputable def biproductSumIso {ι κ : Type} [Fintype ι] [Fintype κ]
    (P : ι → ModuleCat.{max u v} A) (Q : κ → ModuleCat.{max u v} A) :
    (⨁ P) ⊞ (⨁ Q) ≅ ⨁ (Sum.elim P Q) := by
  let M : ι ⊕ κ → ModuleCat.{max u v} A := Sum.elim P Q
  exact ModuleCat.biprodIsoProd _ _ ≪≫
    (((ModuleCat.biproductIsoPi P).toLinearEquiv.prodCongr
      (ModuleCat.biproductIsoPi Q).toLinearEquiv).toModuleIso) ≪≫
    (LinearEquiv.sumPiEquivProdPi A ι κ (fun j => ↥(M j))).symm.toModuleIso ≪≫
    (ModuleCat.biproductIsoPi M).symm

/-- Every finite-dimensional module has a decomposition into finitely many
nonzero indecomposable finite-dimensional modules. The zero module has an
empty decomposition. The finite index type is in `Type`, independently of
the universes of the field and algebra. -/
theorem exists_finite_indecomposable_biproduct (W : FiniteModule k A) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → IndecomposableModule k A),
      Nonempty (W.val ≅ ⨁ fun i => (P i).obj) := by
  classical
  generalize hn : Module.finrank k W.val = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    by_cases hzero : IsZero W.val
    · let P : PEmpty → IndecomposableModule k A := PEmpty.elim
      refine ⟨PEmpty, inferInstance, P, ⟨?_⟩⟩
      have hpi : IsZero (ModuleCat.of A (∀ i : PEmpty, (P i).obj)) :=
        ModuleCat.isZero_iff_subsingleton.mpr inferInstance
      exact hzero.iso (hpi.of_iso (ModuleCat.biproductIsoPi (fun i => (P i).obj)))
    by_cases hind : Indecomposable W.val
    · let P : Unit → IndecomposableModule k A := fun _ => ⟨W, hind⟩
      exact ⟨Unit, inferInstance, P, ⟨(biproductUniqueIso (fun i => (P i).obj)).symm⟩⟩
    obtain ⟨U, V, e, hU, hV⟩ := exists_smaller_biprod W hzero hind
    obtain ⟨ι, hι, P, ⟨eU⟩⟩ := ih (Module.finrank k U.val) (by omega) U rfl
    obtain ⟨κ, hκ, Q, ⟨eV⟩⟩ := ih (Module.finrank k V.val) (by omega) V rfl
    let := hι
    let := hκ
    refine ⟨ι ⊕ κ, inferInstance, Sum.elim P Q, ⟨?_⟩⟩
    rw [show (fun i => (Sum.elim P Q i).obj) =
      Sum.elim (fun i => (P i).obj) (fun j => (Q j).obj) from
        funext fun i => by cases i <;> rfl]
    exact e ≪≫ biprod.mapIso eU eV ≪≫
      biproductSumIso (fun i => (P i).obj) (fun j => (Q j).obj)

/-- The same existence theorem with canonical finite indices, as in the
manuscript's finite direct-sum notation. All summands carry their proved
finite-dimensionality and indecomposability. -/
theorem exists_indecomposable_biproduct (W : FiniteModule k A) :
    ∃ (n : ℕ) (P : Fin n → IndecomposableModule k A),
      Nonempty (W.val ≅ ⨁ fun i => (P i).obj) := by
  classical
  obtain ⟨ι, hι, P, ⟨e⟩⟩ := exists_finite_indecomposable_biproduct W
  let := hι
  let ε := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, P ∘ ε,
    ⟨e ≪≫ (biproduct.reindex ε (fun i => (P i).obj)).symm⟩⟩

/-- Dimensions add in an actual finite indecomposable decomposition. -/
theorem finrank_eq_sum_of_indecomposable_biproduct
    (W : FiniteModule k A) {n : ℕ} (P : Fin n → IndecomposableModule k A)
    (e : W.val ≅ ⨁ fun i => (P i).obj) :
    Module.finrank k W.val = ∑ i, Module.finrank k (P i).obj := by
  let : ∀ i, Module.Finite k (P i).obj := fun i => (P i).val.property
  have h := ((e ≪≫ ModuleCat.biproductIsoPi (fun i => (P i).obj)).toLinearEquiv.restrictScalars
    k).finrank_eq
  exact h.trans (Module.finrank_pi_fintype k)

/-- Nonzero summands give a dimension bound on their number, without
assuming uniqueness of the decomposition. -/
theorem number_summands_le_finrank
    (W : FiniteModule k A) {n : ℕ} (P : Fin n → IndecomposableModule k A)
    (e : W.val ≅ ⨁ fun i => (P i).obj) :
    n ≤ Module.finrank k W.val := by
  rw [finrank_eq_sum_of_indecomposable_biproduct W P e]
  have hpos (i : Fin n) : 1 ≤ Module.finrank k (P i).obj := by
    let : Module.Finite k (P i).obj := (P i).val.property
    let : Nontrivial (P i).obj := not_subsingleton_iff_nontrivial.mp
      (fun hs => (P i).property.1 (ModuleCat.isZero_iff_subsingleton.mpr hs))
    exact Module.finrank_pos
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => hpos i

/-- An indecomposable retract of a finite sum of indecomposables is
isomorphic to one of those summands. This is the first matching step in
the uniqueness argument, derived from the radical rather than assumed. -/
theorem exists_isIso_component_of_retract
    {X : IndecomposableModule k A} {n : ℕ} (P : Fin n → IndecomposableModule k A)
    (a : X.obj ⟶ ⨁ fun i => (P i).obj)
    (b : (⨁ fun i => (P i).obj) ⟶ X.obj) (hab : a ≫ b = 𝟙 X.obj) :
    ∃ i, IsIso (a ≫ biproduct.π (fun j => (P j).obj) i) := by
  classical
  by_contra h
  push Not at h
  have hrad (i : Fin n) : IsRadical A (a ≫ biproduct.π (fun j => (P j).obj) i) :=
    (isRadical_iff_not_isIso (X := X) (Y := P i) _).mpr (h i)
  have hsum : a ≫ b = ∑ i,
      (a ≫ biproduct.π (fun j => (P j).obj) i) ≫
        (biproduct.ι (fun j => (P j).obj) i ≫ b) := by
    calc
      a ≫ b = a ≫ (∑ i, biproduct.π (fun j => (P j).obj) i ≫
          biproduct.ι (fun j => (P j).obj) i) ≫ b := by
        rw [biproduct.total, Category.id_comp]
      _ = _ := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  have hr : IsRadical A (a ≫ b) := by
    rw [hsum]
    exact isRadical_sum Finset.univ _ fun i _ => (hrad i).postcomp _
  exact X.property.1 (isRadical_id_iff_isZero.mp (hab ▸ hr))

/-- The ordinary direct-summand relation, stated using a split inclusion. -/
def IsIndecomposableSummand (X : IndecomposableModule k A) (W : FiniteModule k A) : Prop :=
  ∃ (a : X.obj ⟶ W.val) (b : W.val ⟶ X.obj), a ≫ b = 𝟙 X.obj

/-- Every indecomposable summand is matched to a component in any chosen
decomposition. The statement does not depend on uniqueness of multiplicities. -/
theorem isIndecomposableSummand_iff_component_iso
    (X : IndecomposableModule k A) (W : FiniteModule k A)
    {n : ℕ} (P : Fin n → IndecomposableModule k A)
    (e : W.val ≅ ⨁ fun i => (P i).obj) :
    IsIndecomposableSummand X W ↔ ∃ i, Nonempty (X.obj ≅ (P i).obj) := by
  constructor
  · rintro ⟨a, b, hab⟩
    obtain ⟨i, hi⟩ := exists_isIso_component_of_retract P (a ≫ e.hom) (e.inv ≫ b)
      (by simpa using hab)
    let := hi
    exact ⟨i, ⟨asIso ((a ≫ e.hom) ≫ biproduct.π (fun j => (P j).obj) i)⟩⟩
  · rintro ⟨i, ⟨h⟩⟩
    refine ⟨h.hom ≫ biproduct.ι (fun j => (P j).obj) i ≫ e.inv,
      e.hom ≫ biproduct.π (fun j => (P j).obj) i ≫ h.inv, ?_⟩
    simp

/-- Isomorphic modules have the same indecomposable summands. -/
theorem isIndecomposableSummand_iff_of_iso
    (X : IndecomposableModule k A) {W V : FiniteModule k A} (e : W.val ≅ V.val) :
    IsIndecomposableSummand X W ↔ IsIndecomposableSummand X V := by
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨a ≫ e.hom, e.inv ≫ b, by simpa using hab⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨a ≫ e.inv, e.hom ≫ b, by simpa using hab⟩

/-- Two decompositions of the same module have the same indecomposable
isomorphism classes. Full matching with multiplicities is a separate
Krull--Schmidt uniqueness obligation. -/
theorem component_iso_iff_of_decompositions
    (X : IndecomposableModule k A) (W : FiniteModule k A)
    {n m : ℕ} (P : Fin n → IndecomposableModule k A)
    (Q : Fin m → IndecomposableModule k A)
    (eP : W.val ≅ ⨁ fun i => (P i).obj) (eQ : W.val ≅ ⨁ fun i => (Q i).obj) :
    (∃ i, Nonempty (X.obj ≅ (P i).obj)) ↔ ∃ j, Nonempty (X.obj ≅ (Q j).obj) :=
  (isIndecomposableSummand_iff_component_iso X W P eP).symm.trans
    (isIndecomposableSummand_iff_component_iso X W Q eQ)

end C3PerfectField
