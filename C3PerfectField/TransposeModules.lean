module

public import C3PerfectField.ModuleDuality

/-!
The module-valued transpose of the chosen minimal projective presentation,
and its dimension-preserving field dual. The quotient uses the right
`A`-action on `Hom_A(P,A)`. Almost split existence and the identification of
its kernel with this module are separate, still unproved obligations.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory
open scoped ModuleCat

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- The usual right module of maps to the regular left module. -/
abbrev regularHom (P : FiniteModule k A) := P.val →ₗ[A] A

/-- Compare the regular module `A` with the universe-compatible `A^1`
already used for the proved hom-space estimates. -/
def regularHomToBundled [FiniteDimensional k A] (P : FiniteModule k A) :
    regularHom P →ₗ[k] (P.val ⟶ (regularFiniteModule (k := k) (A := A)).val) where
  toFun := fun f => ModuleCat.ofHom {
    toFun := fun x _ => ULift.up (f x)
    map_add' := by intro x y; ext i; exact f.map_add x y
    map_smul' := by
      intro a x
      ext i
      exact f.map_smul a x
  }
  map_add' := by intro f g; rfl
  map_smul' := by
    intro c f
    apply ModuleCat.hom_ext
    ext x i
    change c • f x = algebraMap k A c * f x
    exact Algebra.smul_def c (f x)

theorem regularHomToBundled_injective [FiniteDimensional k A] (P : FiniteModule k A) :
    Function.Injective (regularHomToBundled (k := k) P) := by
  intro f g h
  ext x
  exact congrArg (fun q => (q.hom x (0 : Fin 1)).down) h

theorem finite_regularHom [FiniteDimensional k A] (P : FiniteModule k A) :
    Module.Finite k (regularHom P) := by
  let : Module.Finite k (P.val ⟶ (regularFiniteModule (k := k) (A := A)).val) :=
    finite_module_hom _ _
  exact FiniteDimensional.of_injective (regularHomToBundled P)
    (regularHomToBundled_injective P)

namespace MinimalProjectivePresentation

variable {X : FiniteModule k A} (T : MinimalProjectivePresentation X)

/-- Precomposition with the differential is right `A`-linear: right
multiplication takes place in the regular target of each homomorphism. -/
def transposeMap : regularHom T.P₀ →ₗ[Aᵐᵒᵖ] regularHom T.P₁ where
  toFun := fun f => f.comp T.differential.hom
  map_add' := by intro f g; rfl
  map_smul' := by intro a f; rfl

theorem transposeMap_apply (f : regularHom T.P₀) (x : T.P₁.val) :
    T.transposeMap f x = f (T.differential.hom x) := rfl

/-- The actual right-module cokernel of `Hom_A(P₀,A) → Hom_A(P₁,A)`. -/
abbrev transposeCarrier := regularHom T.P₁ ⧸ LinearMap.range T.transposeMap

def transposeModule : ModuleCat.{max u v} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ T.transposeCarrier

def transposeScalarEquiv : T.transposeModule ≃ₗ[k] T.transposeCarrier where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro c x
    change T.transposeCarrier at x
    change (algebraMap k Aᵐᵒᵖ c) • x = c • x
    exact IsScalarTower.algebraMap_smul Aᵐᵒᵖ c x

theorem finite_transposeCarrier [FiniteDimensional k A] :
    Module.Finite k T.transposeCarrier := by
  let : Module.Finite k (regularHom T.P₁) := finite_regularHom T.P₁
  exact Module.Finite.equiv
    (Submodule.Quotient.restrictScalarsEquiv k (LinearMap.range T.transposeMap))

theorem finite_transposeModule [FiniteDimensional k A] :
    Module.Finite k T.transposeModule := by
  let : Module.Finite k T.transposeCarrier := T.finite_transposeCarrier
  exact Module.Finite.equiv T.transposeScalarEquiv.symm

def finiteTransposeModule [FiniteDimensional k A] : FiniteModule k Aᵐᵒᵖ :=
  ⟨T.transposeModule, T.finite_transposeModule⟩

theorem finrank_regularHom_P₁_le [FiniteDimensional k A] :
    Module.finrank k (regularHom T.P₁) ≤
      (Module.finrank k A) ^ 2 * Module.finrank k X.val := by
  let : Module.Finite k (T.P₁.val ⟶ (regularFiniteModule (k := k) (A := A)).val) :=
    finite_module_hom _ _
  have h := (LinearMap.finrank_le_finrank_of_injective
    (regularHomToBundled_injective (k := k) T.P₁)).trans
    (T.finrank_hom_P₁_le (regularFiniteModule (k := k) (A := A)))
  simpa only [finrank_regularFiniteModule, pow_two] using h

/-- The manuscript's transpose bound for the genuine right module. -/
theorem finrank_transposeModule_le [FiniteDimensional k A] :
    Module.finrank k T.transposeModule ≤
      (Module.finrank k A) ^ 2 * Module.finrank k X.val := by
  let : Module.Finite k (regularHom T.P₁) := finite_regularHom T.P₁
  rw [T.transposeScalarEquiv.finrank_eq,
    ← (Submodule.Quotient.restrictScalarsEquiv k (LinearMap.range T.transposeMap)).finrank_eq]
  exact (Submodule.finrank_quotient_le
    ((LinearMap.range T.transposeMap).restrictScalars k)).trans
    T.finrank_regularHom_P₁_le

/-- The actual left module `D Tr X`, relative to the chosen presentation. -/
def dualTransposeModule [FiniteDimensional k A] : FiniteModule k A :=
  finiteRightDualModule T.finiteTransposeModule

/-- Field dualization preserves the dimension of the genuine transpose. -/
theorem finrank_dualTransposeModule [FiniteDimensional k A] :
    Module.finrank k T.dualTransposeModule.val = Module.finrank k T.transposeModule := by
  exact finrank_rightDualModule T.finiteTransposeModule

theorem finrank_dualTransposeModule_le [FiniteDimensional k A] :
    Module.finrank k T.dualTransposeModule.val ≤
      (Module.finrank k A) ^ 2 * Module.finrank k X.val := by
  rw [T.finrank_dualTransposeModule]
  exact T.finrank_transposeModule_le

end MinimalProjectivePresentation
end C3PerfectField
