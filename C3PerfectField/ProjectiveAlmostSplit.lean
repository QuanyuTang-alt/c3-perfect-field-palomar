module

public import C3PerfectField.ProjectiveCovers
public import C3PerfectField.AlmostSplitPredecessors
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RingTheory.Jacobson.Semiprimary

/-!
The projective case in manuscript `ext:ar` and `prop:local`.
An indecomposable finite projective module has a unique maximal submodule.
Its inclusion is right almost split, with source dimension at most that of
the projective module. All factorization statements use actual module maps.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

def submoduleModule (M : FiniteModule k A) (N : Submodule A M.val) :
    ModuleCat.{max u v} A := ModuleCat.of A N

def submoduleInclusion (M : FiniteModule k A) (N : Submodule A M.val) :
    submoduleModule M N ⟶ M.val := ModuleCat.ofHom N.subtype

theorem finite_submoduleModule (M : FiniteModule k A) (N : Submodule A M.val) :
    Module.Finite k (submoduleModule M N) := by
  let : Module.Finite k M.val := M.property
  exact FiniteDimensional.of_injective
    ((submoduleInclusion M N).hom.restrictScalars k) Subtype.val_injective

def finiteSubmoduleModule (M : FiniteModule k A) (N : Submodule A M.val) :
    FiniteModule k A := ⟨submoduleModule M N, finite_submoduleModule M N⟩

theorem finrank_submoduleModule_le (M : FiniteModule k A) (N : Submodule A M.val) :
    Module.finrank k (submoduleModule M N) ≤ Module.finrank k M.val := by
  let : Module.Finite k M.val := M.property
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (submoduleInclusion M N).hom.restrictScalars k) Subtype.val_injective

theorem submoduleInclusion_not_isSplitEpi (M : FiniteModule k A)
    (N : Submodule A M.val) (hN : N ≠ ⊤) :
    ¬IsSplitEpi (submoduleInclusion M N) := by
  intro h
  let := h
  have hs := (ModuleCat.epi_iff_surjective (submoduleInclusion M N)).mp inferInstance
  apply hN
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := hs x
  exact hy ▸ y.property

/-- Projectivity and a local endomorphism ring force every nonretraction
into the module to have image in any chosen maximal submodule. -/
theorem range_le_coatom_of_not_isSplitEpi_projective
    (X : IndecomposableModule k A) (hX : Projective X.obj)
    (N : Submodule A X.obj) (hN : IsCoatom N)
    (Y : FiniteModule k A) (f : Y.val ⟶ X.obj) (hf : ¬IsSplitEpi f) :
    LinearMap.range f.hom ≤ N := by
  let := hX
  let := isLocalRing_end_of_finite_indecomposable X
  let Q : ModuleCat.{max u v} A := ModuleCat.of A (X.obj ⧸ N)
  let q : X.obj ⟶ Q := ModuleCat.ofHom N.mkQ
  let : IsSimpleModule A (X.obj ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  by_contra hle
  have hne : q.hom.comp f.hom ≠ 0 := by
    intro hz
    apply hle
    rintro x ⟨y, rfl⟩
    have hz' := LinearMap.congr_fun hz y
    change N.mkQ (f.hom y) = 0 at hz'
    exact (Submodule.Quotient.mk_eq_zero N).mp hz'
  have hepi : Epi (f ≫ q) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (LinearMap.surjective_of_ne_zero hne)
  let := hepi
  let s := Projective.factorThru q (f ≫ q)
  let a : X.obj ⟶ X.obj := s ≫ f
  have haq : a ≫ q = q := by
    simpa only [a, Category.assoc] using Projective.factorThru_comp q (f ≫ q)
  have hqne : q ≠ 0 := by
    intro hq
    apply hN.1
    apply top_unique
    intro x _
    have hz := congrArg (fun t : X.obj ⟶ Q => t.hom x) hq
    exact (Submodule.Quotient.mk_eq_zero N).mp hz
  have haunit : IsUnit (End.of a) := by
    by_contra ha
    have hu := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (End.of a) ha
    let : IsIso (𝟙 X.obj - a) := (isUnit_iff_isIso _).mp hu
    have hz : (𝟙 X.obj - a) ≫ q = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, haq, sub_self]
    apply hqne
    calc
      q = inv (𝟙 X.obj - a) ≫ ((𝟙 X.obj - a) ≫ q) := by
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      _ = 0 := by rw [hz, comp_zero]
  let : IsIso a := (isUnit_iff_isIso _).mp haunit
  apply hf
  refine IsSplitEpi.mk' ⟨inv a ≫ s, ?_⟩
  rw [Category.assoc]
  change inv a ≫ a = 𝟙 X.obj
  simp

/-- A maximal submodule exists because the projective is nonzero and
finite; no finiteness or semiperfectness premise is added to the theorem. -/
theorem exists_coatom_finite_indecomposable (X : IndecomposableModule k A) :
    ∃ N : Submodule A X.obj, IsCoatom N := by
  let : Module.Finite k X.obj := X.val.property
  let : Module.Finite A X.obj := Module.Finite.of_restrictScalars_finite k A X.obj
  let : Nontrivial X.obj := not_subsingleton_iff_nontrivial.mp
    (fun h => X.property.1 (ModuleCat.isZero_iff_subsingleton.mpr h))
  obtain ⟨N, hN, _⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule A X.obj)).resolve_left bot_ne_top
  exact ⟨N, hN⟩

theorem submodule_le_coatom_projective (X : IndecomposableModule k A)
    (hX : Projective X.obj) (N : Submodule A X.obj) (hN : IsCoatom N)
    (L : Submodule A X.obj) (hL : L ≠ ⊤) : L ≤ N := by
  have h := range_le_coatom_of_not_isSplitEpi_projective X hX N hN
    (finiteSubmoduleModule X.val L) (submoduleInclusion X.val L)
    (submoduleInclusion_not_isSplitEpi X.val L hL)
  intro x hx
  exact h ⟨⟨x, hx⟩, rfl⟩

theorem coatom_eq_jacobson_projective (X : IndecomposableModule k A)
    (hX : Projective X.obj) (N : Submodule A X.obj) (hN : IsCoatom N) :
    N = Module.jacobson A X.obj := by
  apply le_antisymm
  · apply le_sInf
    intro L hL
    exact submodule_le_coatom_projective X hX L hL N hN.1
  · exact sInf_le hN

/-- Over the finite-dimensional algebra, the module radical really is
the ideal multiple `J(A) M` used in the manuscript. -/
theorem module_jacobson_eq_ring_jacobson_smul [FiniteDimensional k A]
    (M : FiniteModule k A) :
    Module.jacobson A M.val = Ring.jacobson A • (⊤ : Submodule A M.val) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  let : IsSemisimpleModule A
      (M.val ⧸ Ring.jacobson A • (⊤ : Submodule A M.val)) :=
    TauCeti.isSemisimpleModule_quotient_jacobson_smul_top A M.val
  exact le_antisymm
    (Module.jacobson_le_of_eq_bot
      (IsSemisimpleModule.jacobson_eq_bot A
        (M.val ⧸ Ring.jacobson A • (⊤ : Submodule A M.val))))
    (Ring.jacobson_smul_top_le A M.val)

/-- The actual radical submodule of a finite indecomposable projective
has a right almost split inclusion, including when that radical is zero. -/
theorem isRightAlmostSplit_jacobsonInclusion_projective
    (X : IndecomposableModule k A) (hX : Projective X.obj) :
    IsRightAlmostSplit (k := k)
      (E := finiteSubmoduleModule X.val (Module.jacobson A X.obj))
      (X := X.val)
      (submoduleInclusion X.val (Module.jacobson A X.obj)) := by
  obtain ⟨N, hN⟩ := exists_coatom_finite_indecomposable X
  have heq := coatom_eq_jacobson_projective X hX N hN
  rw [← heq]
  refine ⟨submoduleInclusion_not_isSplitEpi X.val N hN.1, ?_⟩
  intro Y f hf
  have hle := range_le_coatom_of_not_isSplitEpi_projective X hX N hN Y f hf
  refine ⟨ModuleCat.ofHom (f.hom.codRestrict N fun y => hle ⟨y, rfl⟩), ?_⟩
  apply ModuleCat.hom_ext
  rfl

theorem finite_arPredecessors_projective (X : IndecomposableModule k A)
    (hX : Projective X.obj) :
    Set.Finite {y : ARVertex k A | ARArrow k A y (Quotient.mk _ X)} :=
  finite_arPredecessors_of_rightAlmostSplit
    (E := finiteSubmoduleModule X.val (Module.jacobson A X.obj))
    (submoduleInclusion X.val (Module.jacobson A X.obj))
    (isRightAlmostSplit_jacobsonInclusion_projective X hX)

/-- The full predecessor sum in the projective case is at most `dim X`,
which is stronger than the required `C_A * dim X` bound. -/
theorem arPredecessor_sum_le_dimension_projective (X : IndecomposableModule k A)
    (hX : Projective X.obj) :
    ∑ y ∈ (finite_arPredecessors_projective X hX).toFinset,
      arDimension y ≤ Module.finrank k X.obj := by
  exact (arPredecessor_sum_le_source_dimension
    (E := finiteSubmoduleModule X.val (Module.jacobson A X.obj))
    (submoduleInclusion X.val (Module.jacobson A X.obj))
    (isRightAlmostSplit_jacobsonInclusion_projective X hX)).trans
      (finrank_submoduleModule_le X.val (Module.jacobson A X.obj))

end C3PerfectField
