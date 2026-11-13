module

public import C3PerfectField.MainStatement
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.BigOperators.Fin

/-!
The categorical radical used in the target statement, following the elementary
proof of manuscript Lemma `lem:radical-ideal`. No finiteness or
indecomposability assumption is needed for its ideal properties.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory
open scoped ModuleCat BigOperators

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

section Inverse

variable {C : Type*} [Category C] [Preadditive C] {X Y : C}

/-- The inverse is `1 + b (1 - ab)⁻¹ a`, in categorical composition order. -/
theorem isIso_id_sub_comp_swap (a : X ⟶ Y) (b : Y ⟶ X)
    [IsIso (𝟙 X - a ≫ b)] : IsIso (𝟙 Y - b ≫ a) := by
  let s := inv (𝟙 X - a ≫ b)
  refine ⟨𝟙 Y + b ≫ s ≫ a, ?_, ?_⟩
  · calc
      (𝟙 Y - b ≫ a) ≫ (𝟙 Y + b ≫ s ≫ a) =
          𝟙 Y + b ≫ ((𝟙 X - a ≫ b) ≫ s - 𝟙 X) ≫ a := by
        simp only [Preadditive.comp_add, Preadditive.sub_comp, Preadditive.comp_sub,
          Category.assoc, Category.id_comp, Category.comp_id]
        abel
      _ = 𝟙 Y := by
        rw [show (𝟙 X - a ≫ b) ≫ s = 𝟙 X from IsIso.hom_inv_id _]
        simp
  · calc
      (𝟙 Y + b ≫ s ≫ a) ≫ (𝟙 Y - b ≫ a) =
          𝟙 Y + b ≫ (s ≫ (𝟙 X - a ≫ b) - 𝟙 X) ≫ a := by
        simp only [Preadditive.sub_comp, Preadditive.comp_sub,
          Preadditive.add_comp, Category.assoc, Category.id_comp, Category.comp_id]
        abel
      _ = 𝟙 Y := by
        rw [show s ≫ (𝟙 X - a ≫ b) = 𝟙 X from IsIso.inv_hom_id _]
        simp

theorem isIso_id_sub_comp_iff (a : X ⟶ Y) (b : Y ⟶ X) :
    IsIso (𝟙 X - a ≫ b) ↔ IsIso (𝟙 Y - b ≫ a) := by
  constructor
  · intro h
    let := h
    exact isIso_id_sub_comp_swap a b
  · intro h
    let := h
    exact isIso_id_sub_comp_swap b a

end Inverse

variable {P X Y Z : ModuleCat.{max u v} A}

theorem isRadical_zero : IsRadical A (0 : X ⟶ Y) := by
  intro g
  simpa using (inferInstance : IsIso (𝟙 X))

theorem IsRadical.postcomp {f : X ⟶ Y} (hf : IsRadical A f) (b : Y ⟶ Z) :
    IsRadical A (f ≫ b) := by
  intro g
  simpa only [Category.assoc] using hf (b ≫ g)

theorem IsRadical.precomp {f : X ⟶ Y} (hf : IsRadical A f) (a : P ⟶ X) :
    IsRadical A (a ≫ f) := by
  intro g
  exact (isIso_id_sub_comp_iff a (f ≫ g)).mpr (hf (g ≫ a))

theorem IsRadical.add {f f' : X ⟶ Y} (hf : IsRadical A f)
    (hf' : IsRadical A f') : IsRadical A (f + f') := by
  intro g
  let := hf g
  let t := 𝟙 X - f ≫ g
  let := hf' (g ≫ inv t)
  have hfactor :
      𝟙 X - (f + f') ≫ g = (𝟙 X - f' ≫ g ≫ inv t) ≫ t := by
    simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.id_comp,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    dsimp [t]
    abel
  rw [hfactor]
  infer_instance

theorem IsRadical.smul {f : X ⟶ Y} (hf : IsRadical A f) (c : k) :
    IsRadical A (c • f) := by
  simpa using hf.postcomp (c • 𝟙 Y)

theorem isRadical_id_iff_isZero :
    IsRadical A (𝟙 X) ↔ Limits.IsZero X := by
  constructor
  · intro h
    have : IsIso (0 : X ⟶ X) := by simpa using h (𝟙 X)
    exact (Limits.IsZero.iff_id_eq_zero X).mpr
      (by simpa only [Limits.zero_comp] using (IsIso.hom_inv_id (0 : X ⟶ X)).symm)
  · intro h
    rw [h.eq_zero_of_src (𝟙 X)]
    exact isRadical_zero

theorem IsRadical.isZero_of_section {f : X ⟶ Y} (hf : IsRadical A f)
    (g : Y ⟶ X) (hgf : f ≫ g = 𝟙 X) : Limits.IsZero X := by
  apply isRadical_id_iff_isZero.mp
  rw [← hgf]
  exact hf.postcomp g

theorem IsRadical.isZero_of_retraction {f : X ⟶ Y} (hf : IsRadical A f)
    (g : Y ⟶ X) (hgf : g ≫ f = 𝟙 Y) : Limits.IsZero Y := by
  apply isRadical_id_iff_isZero.mp
  rw [← hgf]
  exact hf.precomp g

theorem IsRadical.not_isIso {f : X ⟶ Y} (hf : IsRadical A f)
    (hX : ¬Limits.IsZero X) : ¬IsIso f := by
  intro h
  let := h
  exact hX (hf.isZero_of_section (inv f) (IsIso.hom_inv_id f))

theorem isRadical_sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y))
    (hf : ∀ i ∈ s, IsRadical A (f i)) : IsRadical A (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isRadical_zero (A := A) (X := X) (Y := Y))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The actual radical subspace, allowing the module universe to differ
from the field universe, as needed by scalar extension. -/
def categoricalRadicalSubmodule (X Y : ModuleCat.{max v w} A) : Submodule k (X ⟶ Y) where
  carrier := {f | IsRadical.{w, v} A f}
  zero_mem' := isRadical_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => by
    change IsRadical.{w, v} A (c • f)
    have heq : (c • 𝟙 X) ≫ f = c • f :=
      (Linear.smul_comp X X Y c (𝟙 X) f).trans
        (congrArg (fun q => c • q) (Category.id_comp f))
    rw [← heq]
    exact hf.precomp _

/-- The radical subspace in the universe of the main statement. -/
def radicalSubmodule (X Y : ModuleCat.{max u v} A) : Submodule k (X ⟶ Y) :=
  categoricalRadicalSubmodule.{u, v, u} X Y

@[simp]
theorem mem_radicalSubmodule {f : X ⟶ Y} :
    f ∈ radicalSubmodule (k := k) X Y ↔ IsRadical A f := Iff.rfl

/-- The manuscript's Jacobson criterion, also for noncommutative rings.
Mathlib's general criterion initially supplies a left inverse. Applying it
again to `z - 1` proves that this left inverse is two-sided. -/
theorem mem_jacobson_bot_iff_isUnit_one_sub_mul {R : Type*} [Ring R] (x : R) :
    x ∈ Ideal.jacobson (⊥ : Ideal R) ↔ ∀ y, IsUnit (1 - y * x) := by
  constructor
  · intro hx y
    obtain ⟨z, hz⟩ := Ideal.mem_jacobson_iff.mp hx (-y)
    have hz' : z - z * y * x = 1 := by
      simpa only [Ideal.mem_bot, sub_eq_zero, mul_neg, neg_mul, neg_add_eq_sub] using hz
    have hzmem : z - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
      have heq : z - 1 = z * y * x := by
        calc
          z - 1 = (1 + z * y * x) - 1 :=
            congrArg (fun r => r - 1) (sub_eq_iff_eq_add.mp hz')
          _ = z * y * x := by abel
      rw [heq]
      exact Ideal.mul_mem_left _ (z * y) hx
    obtain ⟨w, hw⟩ := Ideal.mem_jacobson_iff.mp hzmem 1
    have hw' : w * z = 1 := by
      simpa only [Ideal.mem_bot, sub_eq_zero, mul_one, mul_sub, sub_add_cancel] using hw
    have hzt : z * (1 - y * x) = 1 := by
      simpa only [mul_sub, mul_one, ← mul_assoc] using hz'
    have hw_eq : w = 1 - y * x := by
      calc
        w = w * (z * (1 - y * x)) := by rw [hzt, mul_one]
        _ = (w * z) * (1 - y * x) := (mul_assoc _ _ _).symm
        _ = 1 - y * x := by rw [hw', one_mul]
    exact ⟨⟨1 - y * x, z, hw_eq ▸ hw', hzt⟩, rfl⟩
  · intro hx
    apply Ideal.mem_jacobson_iff.mpr
    intro y
    obtain ⟨z, hz⟩ := (hx (-y)).exists_left_inv
    refine ⟨z, ?_⟩
    have hz' : z * y * x + z = 1 := by
      simpa only [neg_mul, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc,
        add_comm] using hz
    simpa only [Ideal.mem_bot, sub_eq_zero] using hz'

theorem isRadical_end_iff_mem_jacobson (f : X ⟶ X) :
    IsRadical A f ↔ End.of f ∈ Ideal.jacobson (⊥ : Ideal (End X)) := by
  rw [mem_jacobson_bot_iff_isUnit_one_sub_mul]
  constructor
  · intro hf g
    rw [isUnit_iff_isIso]
    exact hf g.asHom
  · intro hf g
    exact (isUnit_iff_isIso _).mp (hf (End.of g))

/-- Every finite radical factorization sum belongs to the radical. -/
theorem IsRadicalSquare.isRadical {f : X ⟶ Y} (hf : IsRadicalSquare k A f) :
    IsRadical A f := by
  obtain ⟨n, W, a, b, hab, rfl⟩ := hf
  exact isRadical_sum Finset.univ _ fun j _ => (hab j).1.postcomp (b j)

theorem isRadicalSquare_zero : IsRadicalSquare k A (0 : X ⟶ Y) := by
  refine ⟨0, Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
    fun j => Fin.elim0 j, ?_⟩
  simp

theorem IsRadicalSquare.precomp {f : X ⟶ Y} (hf : IsRadicalSquare k A f)
    (c : P ⟶ X) : IsRadicalSquare k A (c ≫ f) := by
  obtain ⟨n, W, a, b, hab, rfl⟩ := hf
  refine ⟨n, W, fun j => c ≫ a j, b,
    fun j => ⟨(hab j).1.precomp c, (hab j).2⟩, ?_⟩
  simp [Preadditive.comp_sum, Category.assoc]

theorem IsRadicalSquare.postcomp {f : X ⟶ Y} (hf : IsRadicalSquare k A f)
    (c : Y ⟶ Z) : IsRadicalSquare k A (f ≫ c) := by
  obtain ⟨n, W, a, b, hab, rfl⟩ := hf
  refine ⟨n, W, a, fun j => b j ≫ c,
    fun j => ⟨(hab j).1, (hab j).2.postcomp c⟩, ?_⟩
  simp [Preadditive.sum_comp, Category.assoc]

theorem IsRadicalSquare.smul {f : X ⟶ Y} (hf : IsRadicalSquare k A f) (c : k) :
    IsRadicalSquare k A (c • f) := by
  simpa using hf.postcomp (c • 𝟙 Y)

theorem IsRadicalSquare.add {f f' : X ⟶ Y} (hf : IsRadicalSquare k A f)
    (hf' : IsRadicalSquare k A f') : IsRadicalSquare k A (f + f') := by
  obtain ⟨n, W, a, b, hab, rfl⟩ := hf
  obtain ⟨m, W', a', b', hab', rfl⟩ := hf'
  let t : Fin (n + m) → Σ V : FiniteModule k A, (X ⟶ V.val) × (V.val ⟶ Y) :=
    Fin.addCases (motive := fun _ =>
      Σ V : FiniteModule k A, (X ⟶ V.val) × (V.val ⟶ Y))
      (fun j => ⟨W j, a j, b j⟩) (fun j => ⟨W' j, a' j, b' j⟩)
  have ht_left (i : Fin n) : t (Fin.castAdd m i) = ⟨W i, a i, b i⟩ :=
    Fin.addCases_left i
  have ht_right (i : Fin m) : t (Fin.natAdd n i) = ⟨W' i, a' i, b' i⟩ :=
    Fin.addCases_right i
  let radicalPair (s : Σ V : FiniteModule k A, (X ⟶ V.val) × (V.val ⟶ Y)) : Prop :=
    IsRadical A s.2.1 ∧ IsRadical A s.2.2
  let composePair (s : Σ V : FiniteModule k A, (X ⟶ V.val) × (V.val ⟶ Y)) :
      X ⟶ Y := s.2.1 ≫ s.2.2
  refine ⟨n + m, fun j => (t j).1, fun j => (t j).2.1,
    fun j => (t j).2.2, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · change radicalPair (t (Fin.castAdd m i))
      rw [ht_left]
      exact hab i
    · change radicalPair (t (Fin.natAdd n i))
      rw [ht_right]
      exact hab' i
  · change _ = ∑ j, composePair (t j)
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [ht_left]
    · apply Finset.sum_congr rfl
      intro i _
      rw [ht_right]

/-- The radical square is a subspace, with the manuscript's finite-sum
membership criterion unchanged. -/
def radicalSquareSubmodule (X Y : ModuleCat.{max u v} A) : Submodule k (X ⟶ Y) where
  carrier := {f | IsRadicalSquare k A f}
  zero_mem' := isRadicalSquare_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c

@[simp]
theorem mem_radicalSquareSubmodule {f : X ⟶ Y} :
    f ∈ radicalSquareSubmodule (k := k) X Y ↔ IsRadicalSquare k A f := Iff.rfl

theorem radicalSquareSubmodule_le (X Y : ModuleCat.{max u v} A) :
    radicalSquareSubmodule (k := k) X Y ≤ radicalSubmodule (k := k) X Y :=
  fun _ hf => hf.isRadical

theorem isRadicalSquare_sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y))
    (hf : ∀ i ∈ s, IsRadicalSquare k A (f i)) :
    IsRadicalSquare k A (∑ i ∈ s, f i) :=
  (radicalSquareSubmodule (k := k) X Y).sum_mem hf

/-- Transport through module isomorphisms preserves the radical. -/
theorem isRadical_iso_iff (e : P ≅ X) (d : Y ≅ Z) (f : X ⟶ Y) :
    IsRadical A (e.hom ≫ f ≫ d.hom) ↔ IsRadical A f := by
  constructor
  · intro h
    simpa using (h.precomp e.inv).postcomp d.inv
  · intro h
    exact (h.postcomp d.hom).precomp e.hom

/-- Transport preserves the radical square, including its intermediate
finite-dimensional modules. -/
theorem isRadicalSquare_iso_iff (e : P ≅ X) (d : Y ≅ Z) (f : X ⟶ Y) :
    IsRadicalSquare k A (e.hom ≫ f ≫ d.hom) ↔ IsRadicalSquare k A f := by
  constructor
  · intro h
    simpa using (h.precomp e.inv).postcomp d.inv
  · intro h
    exact (h.postcomp d.hom).precomp e.hom

theorem hasARArrow_iso_iff {X X' Y Y' : IndecomposableModule k A}
    (e : X.obj ≅ X'.obj) (d : Y.obj ≅ Y'.obj) :
    HasARArrow k A X Y ↔ HasARArrow k A X' Y' := by
  constructor
  · rintro ⟨f, hf, hf2⟩
    refine ⟨e.inv ≫ f ≫ d.hom, (isRadical_iso_iff e.symm d f).mpr hf, ?_⟩
    exact fun h => hf2 ((isRadicalSquare_iso_iff e.symm d f).mp h)
  · rintro ⟨f, hf, hf2⟩
    refine ⟨e.hom ≫ f ≫ d.inv, (isRadical_iso_iff e d.symm f).mpr hf, ?_⟩
    exact fun h => hf2 ((isRadicalSquare_iso_iff e d.symm f).mp h)

/-- The quotient arrow relation agrees with the arrow criterion on every
pair of representatives, rather than only on some chosen representatives. -/
theorem arArrow_mk_iff (X Y : IndecomposableModule k A) :
    ARArrow k A (Quotient.mk _ X) (Quotient.mk _ Y) ↔ HasARArrow k A X Y := by
  constructor
  · rintro ⟨X', Y', hx, hy, h⟩
    obtain ⟨e⟩ := Quotient.exact hx
    obtain ⟨d⟩ := Quotient.exact hy
    exact (hasARArrow_iso_iff e d).mp h
  · intro h
    exact ⟨X, Y, rfl, rfl, h⟩

/-- The quotient vector space `rad(X,Y) / rad²(X,Y)` from the manuscript.
The square is restricted to the radical through its submodule inclusion. -/
@[instance_reducible]
def IrreducibleSpace (X Y : ModuleCat.{max u v} A) :=
  radicalSubmodule (k := k) X Y ⧸
    (radicalSquareSubmodule (k := k) X Y).comap
      (radicalSubmodule (k := k) X Y).subtype

instance irreducibleSpaceAddCommGroup (X Y : ModuleCat.{max u v} A) :
    AddCommGroup (IrreducibleSpace (k := k) X Y) :=
  inferInstanceAs (AddCommGroup
    (radicalSubmodule (k := k) X Y ⧸
      (radicalSquareSubmodule (k := k) X Y).comap
        (radicalSubmodule (k := k) X Y).subtype))

instance irreducibleSpaceModule (X Y : ModuleCat.{max u v} A) :
    Module k (IrreducibleSpace (k := k) X Y) :=
  inferInstanceAs (Module k
    (radicalSubmodule (k := k) X Y ⧸
      (radicalSquareSubmodule (k := k) X Y).comap
        (radicalSubmodule (k := k) X Y).subtype))

theorem hasARArrow_iff_nontrivial_irreducibleSpace (X Y : IndecomposableModule k A) :
    HasARArrow k A X Y ↔ Nontrivial (IrreducibleSpace (k := k) X.obj Y.obj) := by
  change (∃ f, IsRadical A f ∧ ¬IsRadicalSquare k A f) ↔
    Nontrivial (radicalSubmodule (k := k) X.obj Y.obj ⧸
      (radicalSquareSubmodule (k := k) X.obj Y.obj).comap
        (radicalSubmodule (k := k) X.obj Y.obj).subtype)
  simp only [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.eq_top_iff']
  constructor
  · rintro ⟨f, hf, hf2⟩ h
    exact hf2 (h ⟨f, hf⟩)
  · intro h
    classical
    push Not at h
    obtain ⟨⟨f, hf⟩, hf2⟩ := h
    exact ⟨f, hf, hf2⟩

end C3PerfectField
