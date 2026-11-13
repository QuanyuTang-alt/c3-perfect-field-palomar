module

public import C3PerfectField.ProjectiveCovers

/-!
Dimension estimates for actual `A`-module hom spaces. A projective cover
of `X` is a retract of `A^(dim_k X)`, so its hom space into `V` embeds into
`V^(dim_k X)`. This is the hom-space step in `lem:transpose-bound`.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- The standard generator of a finite free module. -/
noncomputable def finiteFreeGenerator (n : ℕ) (i : Fin n) :
    finiteFreeModule k A n :=
  Pi.single i (ULift.up 1)

omit [Field k] [Algebra k A] in
theorem finiteFree_sum_generators (n : ℕ) (a : finiteFreeModule k A n) :
    a = ∑ i, (a i).down • finiteFreeGenerator (k := k) (A := A) n i := by
  classical
  funext j
  apply ULift.ext
  change (a j).down =
    ((∑ i : Fin n, (a i).down • Pi.single i (ULift.up (1 : A)) :
      Fin n → ULift.{u} A) j).down
  simp [Finset.sum_apply, Pi.single_apply]

/-- An `A`-linear map out of a finite free module is determined by its
values on the standard generators. Evaluation is linear over the base field. -/
noncomputable def finiteFreeHomEvaluation (n : ℕ) (V : ModuleCat.{max u v} A) :
    (finiteFreeModule k A n ⟶ V) →ₗ[k] (Fin n → V) where
  toFun := fun f i => f (finiteFreeGenerator (k := k) (A := A) n i)
  map_add' := by
    intro f g
    ext i
    rfl
  map_smul' := by
    intro c f
    ext i
    rfl

theorem finiteFreeHomEvaluation_injective (n : ℕ) (V : ModuleCat.{max u v} A) :
    Function.Injective (finiteFreeHomEvaluation (k := k) (A := A) n V) := by
  intro f g hfg
  apply ModuleCat.hom_ext
  ext a
  rw [finiteFree_sum_generators n a]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show f.hom (finiteFreeGenerator (k := k) (A := A) n i) =
    g.hom (finiteFreeGenerator (k := k) (A := A) n i) from congrFun hfg i]

theorem finite_hom_finiteFreeModule (n : ℕ) (V : FiniteModule k A) :
    Module.Finite k (finiteFreeModule k A n ⟶ V.val) := by
  let : Module.Finite k V.val := V.property
  exact FiniteDimensional.of_injective (finiteFreeHomEvaluation n V.val)
    (finiteFreeHomEvaluation_injective n V.val)

theorem finrank_hom_finiteFreeModule_le (n : ℕ) (V : FiniteModule k A) :
    Module.finrank k (finiteFreeModule k A n ⟶ V.val) ≤ n * Module.finrank k V.val := by
  let : Module.Finite k V.val := V.property
  have h := LinearMap.finrank_le_finrank_of_injective
    (finiteFreeHomEvaluation_injective (k := k) (A := A) n V.val)
  simpa [Module.finrank_pi_fintype] using h

/-- Hom spaces between finite-dimensional modules are finite-dimensional.
This uses a finite free epimorphism and does not require the algebra to
be finite-dimensional. -/
theorem finite_module_hom (P V : FiniteModule k A) :
    Module.Finite k (P.val ⟶ V.val) := by
  obtain ⟨q, hq⟩ := exists_finiteFree_epi P
  let := hq
  let : Module.Finite k (finiteFreeModule k A (Module.finrank k P.val) ⟶ V.val) :=
    finite_hom_finiteFreeModule _ V
  apply FiniteDimensional.of_injective (Linear.leftComp k V.val q)
  intro f g hfg
  exact (cancel_epi q).mp hfg

/-- Precomposing with the retraction embeds hom spaces from a summand. -/
theorem hom_precompose_retract_injective {P Q V : ModuleCat.{max u v} A}
    (h : Retract P Q) :
    Function.Injective (Linear.leftComp k V h.r) := by
  intro f g hfg
  have h' := congrArg (fun a => h.i ≫ a) hfg
  simpa only [Linear.leftComp_apply, ← Category.assoc, h.retract,
    Category.id_comp] using h'

/-- The sharp estimate needed by the transpose argument: the number of
free generators is `dim_k X`, rather than `dim_k P`. -/
theorem finrank_hom_projectiveCover_le [FiniteDimensional k A]
    {P X : FiniteModule k A} (p : P.val ⟶ X.val)
    (hp : IsProjectiveCover (k := k) p) (V : FiniteModule k A) :
    Module.finrank k (P.val ⟶ V.val) ≤ Module.finrank k X.val * Module.finrank k V.val := by
  obtain ⟨q, hq⟩ := exists_finiteFree_epi X
  let := hq
  let := projective_finiteFreeModule (k := k) (A := A) (Module.finrank k X.val)
  obtain ⟨h⟩ := projectiveCover_retract_of_epi p hp q
  let : Module.Finite k (finiteFreeModule k A (Module.finrank k X.val) ⟶ V.val) :=
    finite_hom_finiteFreeModule _ V
  exact (LinearMap.finrank_le_finrank_of_injective
    (hom_precompose_retract_injective (k := k) (V := V.val) h)).trans
      (finrank_hom_finiteFreeModule_le _ V)

end C3PerfectField
