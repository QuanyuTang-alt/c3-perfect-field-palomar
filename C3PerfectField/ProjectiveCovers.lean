module

public import C3PerfectField.ARDimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
Manuscript `lem:cover-bound`: finite free epimorphisms, the retract property
of projective covers, and their dimension bound.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Finite free `A`-modules in the universe used by the target category. -/
def finiteFreeModule (_k : Type u) (A : Type v) [Ring A] (n : ℕ) :
    ModuleCat.{max u v} A :=
  ModuleCat.of A (Fin n → ULift.{u} A)

/-- A family of vectors gives the usual evaluation map from a finite
free module, with coefficients acting on the left. -/
noncomputable def finiteFreeEvaluation {X : ModuleCat.{max u v} A} {n : ℕ}
    (b : Fin n → X) : finiteFreeModule k A n ⟶ X :=
  ModuleCat.ofHom {
    toFun := fun a => ∑ i, (a i).down • b i
    map_add' := by
      intro a c
      simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro a c
      simp [Finset.smul_sum, smul_smul]
  }

/-- A base-field basis generates the module over `A`. The free module has
exactly `dim_k X` generators, including the empty basis for the zero module. -/
theorem exists_finiteFree_epi (X : FiniteModule k A) :
    ∃ q : finiteFreeModule k A (Module.finrank k X.val) ⟶ X.val, Epi q := by
  classical
  let : Module.Finite k X.val := X.property
  let b := Module.finBasis k X.val
  let q := finiteFreeEvaluation (k := k) (A := A) b
  refine ⟨q, (ModuleCat.epi_iff_surjective q).mpr ?_⟩
  intro x
  refine ⟨fun i => ULift.up (algebraMap k A (b.repr x i)), ?_⟩
  change ∑ i, (algebraMap k A (b.repr x i)) • b i = x
  simpa only [IsScalarTower.algebraMap_smul] using b.sum_repr x

omit [Field k] [Algebra k A] in
theorem projective_finiteFreeModule (n : ℕ) :
    Projective (finiteFreeModule k A n) := by
  change Projective (ModuleCat.of A (Fin n → ULift.{u} A))
  let : Module.Projective A (Fin n → ULift.{u} A) := inferInstance
  infer_instance

/-- The field action supplied by `ModuleCat` agrees with the usual
coordinatewise action by the scalar-tower identity. -/
noncomputable def finiteFreeScalarEquiv (n : ℕ) :
    (finiteFreeModule k A n) ≃ₗ[k] (Fin n → ULift.{u} A) where
  toFun := fun a => a
  invFun := fun a => a
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro c a
    funext i
    change ULift.up ((algebraMap k A c) * (a i).down) = ULift.up (c • (a i).down)
    rw [Algebra.smul_def]

instance finite_finiteFreeModule [FiniteDimensional k A] (n : ℕ) :
    Module.Finite k (finiteFreeModule k A n) :=
  Module.Finite.equiv (finiteFreeScalarEquiv (k := k) (A := A) n).symm

theorem finrank_finiteFreeModule [FiniteDimensional k A] (n : ℕ) :
    Module.finrank k (finiteFreeModule k A n) =
      n * Module.finrank k A := by
  rw [(finiteFreeScalarEquiv (k := k) (A := A) n).finrank_eq]
  simp [Module.finrank_pi_fintype, finrank_ulift]

/-- A projective cover is a projective epimorphism with the usual
endomorphism minimality property used in the manuscript. -/
def IsProjectiveCover {P X : FiniteModule k A} (p : P.val ⟶ X.val) : Prop :=
  Projective P.val ∧ Epi p ∧ ∀ s : P.val ⟶ P.val, s ≫ p = p → IsIso s

/-- A projective cover is a retract of any projective module surjecting
onto the same target, exactly as in manuscript `lem:cover-bound`. -/
theorem projectiveCover_retract_of_epi
    {P X : FiniteModule k A} (p : P.val ⟶ X.val)
    (hp : IsProjectiveCover (k := k) p)
    {Q : ModuleCat.{max u v} A} (q : Q ⟶ X.val) [Projective Q] [Epi q] :
    Nonempty (Retract P.val Q) := by
  let := hp.1
  let := hp.2.1
  let s := Projective.factorThru p q
  let t := Projective.factorThru q p
  have hst : s ≫ t ≫ p = p := by
    rw [Projective.factorThru_comp, Projective.factorThru_comp]
  let := hp.2.2 (s ≫ t) (by simpa only [Category.assoc] using hst)
  exact ⟨{
    i := inv (s ≫ t) ≫ s
    r := t
    retract := by simp
  }⟩

/-- The vector-space dimension estimate follows from an actual retract. -/
theorem finrank_le_of_module_retract
    {P Q : FiniteModule k A} (h : Retract P.val Q.val) :
    Module.finrank k P.val ≤ Module.finrank k Q.val := by
  let : Module.Finite k Q.val := Q.property
  apply LinearMap.finrank_le_finrank_of_injective
    (f := h.i.hom.restrictScalars k)
  intro x y hxy
  have h' := congrArg h.r.hom hxy
  change h.r.hom (h.i.hom x) = h.r.hom (h.i.hom y) at h'
  simpa only [← ModuleCat.comp_apply, h.retract, ModuleCat.id_apply] using h'

/-- Every projective cover satisfies the manuscript's bound, with no
choice of a larger number of free generators. -/
theorem finrank_projectiveCover_le [FiniteDimensional k A]
    {P X : FiniteModule k A} (p : P.val ⟶ X.val)
    (hp : IsProjectiveCover (k := k) p) :
    Module.finrank k P.val ≤ Module.finrank k A * Module.finrank k X.val := by
  obtain ⟨q, hq⟩ := exists_finiteFree_epi X
  let := hq
  let := projective_finiteFreeModule (k := k) (A := A) (Module.finrank k X.val)
  obtain ⟨h⟩ := projectiveCover_retract_of_epi p hp q
  let Q : FiniteModule k A :=
    ⟨finiteFreeModule k A (Module.finrank k X.val), inferInstance⟩
  have hd := finrank_le_of_module_retract (Q := Q) h
  change Module.finrank k P.val ≤ Module.finrank k (finiteFreeModule k A _) at hd
  simpa only [finrank_finiteFreeModule, Nat.mul_comm] using hd

/-- A projective epimorphism with least possible source dimension is a
projective cover. Fitting's decomposition retracts its source onto the
stable range of an endomorphism fixing the epimorphism. Minimal dimension
forces that range to be the entire source. -/
theorem isProjectiveCover_of_minimal_dimension
    {P X : FiniteModule k A} (p : P.val ⟶ X.val)
    (hP : Projective P.val) (hp : Epi p)
    (hmin : ∀ (Q : FiniteModule k A) (q : Q.val ⟶ X.val),
      Projective Q.val → Epi q → Module.finrank k P.val ≤ Module.finrank k Q.val) :
    IsProjectiveCover (k := k) p := by
  refine ⟨hP, hp, ?_⟩
  intro f hfp
  let := hP
  let : Module.Finite k P.val := P.property
  let : IsNoetherian A P.val :=
    isNoetherian_of_tower k (inferInstance : IsNoetherian k P.val)
  let : IsArtinian A P.val :=
    isArtinian_of_tower k (inferInstance : IsArtinian k P.val)
  have hpf : p.hom ∘ₗ f.hom = p.hom := ModuleCat.hom_ext_iff.mp hfp
  have hpow (m : ℕ) : p.hom ∘ₗ f.hom ^ m = p.hom := by
    induction m with
    | zero =>
      change p.hom ∘ₗ LinearMap.id = p.hom
      exact LinearMap.comp_id _
    | succ m ih =>
      simpa only [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih] using hpf
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f.hom)
  let N := LinearMap.ker (f.hom ^ (n + 1))
  let R := LinearMap.range (f.hom ^ (n + 1))
  have hcompl : IsCompl R N := (hn (n + 1) (Nat.le_succ n)).symm
  let U : ModuleCat.{max u v} A := ModuleCat.of A R
  let h : Retract U P.val := {
    i := ModuleCat.ofHom R.subtype
    r := ModuleCat.ofHom (R.projectionOnto N hcompl)
    retract := by
      apply ModuleCat.hom_ext
      exact R.projectionOnto_comp_subtype hcompl
  }
  let : IsSplitMono h.i := ⟨⟨h.splitMono⟩⟩
  let Q : FiniteModule k A := ⟨U, finite_of_isSplitMono (W := P) h.i⟩
  let q : Q.val ⟶ X.val := h.i ≫ p
  have hQ : Projective Q.val := h.projective
  have hq : Epi q := (ModuleCat.epi_iff_surjective q).mpr (by
    intro y
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective p).mp hp y
    refine ⟨⟨(f.hom ^ (n + 1)) x, x, rfl⟩, ?_⟩
    change p.hom ((f.hom ^ (n + 1)) x) = y
    exact (LinearMap.congr_fun (hpow (n + 1)) x).trans hx)
  have hdim : Module.finrank k Q.val = Module.finrank k P.val :=
    Nat.le_antisymm (finrank_le_of_module_retract (P := Q) (Q := P) h)
      (hmin Q q hQ hq)
  let : Module.Finite k Q.val := Q.property
  have hinji : Function.Injective h.i.hom :=
    (ModuleCat.mono_iff_injective h.i).mp inferInstance
  have hsurji : Function.Surjective h.i.hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := h.i.hom.restrictScalars k) hdim).mp hinji
  have hsurjPow : Function.Surjective (f.hom ^ (n + 1)) := by
    intro x
    obtain ⟨z, hz⟩ := hsurji x
    obtain ⟨y, hy⟩ := z.property
    exact ⟨y, hy.trans hz⟩
  have hsurjf : Function.Surjective f.hom := by
    intro x
    obtain ⟨y, hy⟩ := hsurjPow x
    refine ⟨(f.hom ^ n) y, ?_⟩
    simpa only [pow_succ', Module.End.mul_apply] using hy
  have hinjf : Function.Injective f.hom :=
    (LinearMap.injective_iff_surjective (f := f.hom.restrictScalars k)).mpr hsurjf
  exact (LinearEquiv.ofBijective f.hom ⟨hinjf, hsurjf⟩).toModuleIso.isIso_hom

/-- Every finite-dimensional module over a finite-dimensional algebra has
a finite-dimensional projective cover. This proves existence, rather than
taking projective covers as an external assumption. -/
theorem exists_projectiveCover [FiniteDimensional k A] (X : FiniteModule k A) :
    ∃ (P : FiniteModule k A) (p : P.val ⟶ X.val), IsProjectiveCover (k := k) p := by
  classical
  let B : ℕ → Prop := fun n => ∃ (P : FiniteModule k A),
    Module.finrank k P.val = n ∧ ∃ p : P.val ⟶ X.val, Projective P.val ∧ Epi p
  have hex : ∃ n, B n := by
    obtain ⟨q, hq⟩ := exists_finiteFree_epi X
    let P : FiniteModule k A := ⟨finiteFreeModule k A (Module.finrank k X.val), inferInstance⟩
    exact ⟨Module.finrank k P.val, P, rfl, q,
      projective_finiteFreeModule (k := k) (A := A) _, hq⟩
  obtain ⟨P, hdim, p, hP, hp⟩ := Nat.find_spec hex
  refine ⟨P, p, isProjectiveCover_of_minimal_dimension p hP hp ?_⟩
  intro Q q hQ hq
  rw [hdim]
  exact Nat.find_min' hex ⟨Q, rfl, q, hQ, hq⟩

end C3PerfectField
