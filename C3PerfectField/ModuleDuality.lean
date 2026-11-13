module

public import C3PerfectField.TransposeSpaces
public import Mathlib.Algebra.Algebra.Opposite

/-!
 The field duals of left and right modules, with their actual algebra actions.
The bundled base-field action is compared explicitly with the native dual
action, since `ModuleCat.of` supplies its own restricted scalar action.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory
open scoped ModuleCat

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Precomposition by the right action: `(a φ)(x) = φ(x a)`. -/
def rightDualAction (N : ModuleCat.{max u v} Aᵐᵒᵖ) (a : A)
    (φ : Module.Dual k N) : Module.Dual k N where
  toFun := fun x => φ (MulOpposite.op a • x)
  map_add' := by intro x y; simp
  map_smul' := by
    intro c x
    rw [smul_comm (MulOpposite.op a) c x, map_smul]
    rfl

theorem rightDualAction_apply (N : ModuleCat.{max u v} Aᵐᵒᵖ)
    (a : A) (φ : Module.Dual k N) (x : N) :
    rightDualAction N a φ x = φ (MulOpposite.op a • x) := rfl

/-- A left `A`-module structure on the field dual of a right `A`-module. -/
@[instance_reducible]
def rightDualModuleStructure (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    Module A (Module.Dual k N) where
  smul := rightDualAction N
  one_smul := by
    intro φ
    ext x
    change φ (MulOpposite.op (1 : A) • x) = φ x
    simp
  mul_smul := by
    intro a b φ
    ext x
    change φ (MulOpposite.op (a * b) • x) =
      φ (MulOpposite.op b • (MulOpposite.op a • x))
    rw [MulOpposite.op_mul, mul_smul]
  smul_zero := by
    intro a
    ext x
    change (0 : Module.Dual k N) (MulOpposite.op a • x) = 0
    rfl
  smul_add := by intro a φ ψ; ext x; rfl
  add_smul := by
    intro a b φ
    ext x
    change φ (MulOpposite.op (a + b) • x) =
      φ (MulOpposite.op a • x) + φ (MulOpposite.op b • x)
    rw [MulOpposite.op_add, add_smul, map_add]
  zero_smul := by
    intro φ
    ext x
    change φ (MulOpposite.op (0 : A) • x) = 0
    simp

/-- The genuine left module obtained by dualizing a right module over `k`. -/
def rightDualModule (N : ModuleCat.{max u v} Aᵐᵒᵖ) : ModuleCat.{max u v} A :=
  letI := rightDualModuleStructure (k := k) N
  ModuleCat.of A (Module.Dual k N)

/-- Bundling preserves the native vector-space structure, up to this
explicit identity equivalence. -/
def rightDualScalarEquiv (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    rightDualModule (k := k) N ≃ₗ[k] Module.Dual k N where
  toFun := fun φ => φ
  invFun := fun φ => φ
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro c φ
    change Module.Dual k N at φ
    ext x
    change φ (MulOpposite.op (algebraMap k A c) • x) = c • φ x
    change φ (algebraMap k Aᵐᵒᵖ c • x) = c • φ x
    rw [IsScalarTower.algebraMap_smul, map_smul]

theorem finite_rightDualModule (N : FiniteModule k Aᵐᵒᵖ) :
    Module.Finite k (rightDualModule (k := k) N.val) := by
  let : Module.Finite k N.val := N.property
  exact Module.Finite.equiv (rightDualScalarEquiv N.val).symm

def finiteRightDualModule (N : FiniteModule k Aᵐᵒᵖ) : FiniteModule k A :=
  ⟨rightDualModule N.val, finite_rightDualModule N⟩

theorem finrank_rightDualModule (N : FiniteModule k Aᵐᵒᵖ) :
    Module.finrank k (rightDualModule (k := k) N.val) = Module.finrank k N.val := by
  let : Module.Finite k N.val := N.property
  rw [(rightDualScalarEquiv N.val).finrank_eq, Subspace.dual_finrank_eq]

/-- Dualization reverses right-module morphisms and yields actual left-module
morphisms, rather than just base-field linear maps. -/
def rightDualMap {N M : ModuleCat.{max u v} Aᵐᵒᵖ} (f : N ⟶ M) :
    rightDualModule (k := k) M ⟶ rightDualModule (k := k) N := by
  letI := rightDualModuleStructure (k := k) M
  letI := rightDualModuleStructure (k := k) N
  exact ModuleCat.ofHom {
    toFun := fun φ => φ.comp (f.hom.restrictScalars k)
    map_add' := by intro φ ψ; rfl
    map_smul' := by
      intro a φ
      ext x
      change φ (MulOpposite.op a • f.hom x) =
        φ (f.hom (MulOpposite.op a • x))
      rw [f.hom.map_smul]
  }

theorem rightDualMap_id (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    rightDualMap (k := k) (𝟙 N) = 𝟙 (rightDualModule (k := k) N) := by
  apply ModuleCat.hom_ext
  ext φ
  rfl

theorem rightDualMap_comp {N M L : ModuleCat.{max u v} Aᵐᵒᵖ}
    (f : N ⟶ M) (g : M ⟶ L) :
    rightDualMap (k := k) (f ≫ g) = rightDualMap g ≫ rightDualMap f := by
  apply ModuleCat.hom_ext
  ext φ
  rfl

/-- The field dual of a left module has a right action by precomposition. -/
def leftDualAction (M : ModuleCat.{max u v} A) (a : Aᵐᵒᵖ)
    (φ : Module.Dual k M) : Module.Dual k M where
  toFun := fun x => φ (a.unop • x)
  map_add' := by intro x y; simp
  map_smul' := by
    intro c x
    rw [smul_comm a.unop c x, map_smul]
    rfl

@[instance_reducible]
def leftDualModuleStructure (M : ModuleCat.{max u v} A) :
    Module Aᵐᵒᵖ (Module.Dual k M) where
  smul := leftDualAction M
  one_smul := by
    intro φ
    ext x
    change φ ((1 : Aᵐᵒᵖ).unop • x) = φ x
    simp
  mul_smul := by
    intro a b φ
    ext x
    change φ ((a * b).unop • x) = φ (b.unop • (a.unop • x))
    rw [MulOpposite.unop_mul, mul_smul]
  smul_zero := by
    intro a
    ext x
    change (0 : Module.Dual k M) (a.unop • x) = 0
    rfl
  smul_add := by intro a φ ψ; ext x; rfl
  add_smul := by
    intro a b φ
    ext x
    change φ ((a + b).unop • x) = φ (a.unop • x) + φ (b.unop • x)
    rw [MulOpposite.unop_add, add_smul, map_add]
  zero_smul := by
    intro φ
    ext x
    change φ ((0 : Aᵐᵒᵖ).unop • x) = 0
    simp

def leftDualModule (M : ModuleCat.{max u v} A) : ModuleCat.{max u v} Aᵐᵒᵖ :=
  letI := leftDualModuleStructure (k := k) M
  ModuleCat.of Aᵐᵒᵖ (Module.Dual k M)

def leftDualScalarEquiv (M : ModuleCat.{max u v} A) :
    leftDualModule (k := k) M ≃ₗ[k] Module.Dual k M where
  toFun := fun φ => φ
  invFun := fun φ => φ
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro c φ
    change Module.Dual k M at φ
    ext x
    change φ ((algebraMap k Aᵐᵒᵖ c).unop • x) = c • φ x
    change φ (algebraMap k A c • x) = c • φ x
    rw [IsScalarTower.algebraMap_smul, map_smul]

theorem finite_leftDualModule (M : FiniteModule k A) :
    Module.Finite k (leftDualModule (k := k) M.val) := by
  let : Module.Finite k M.val := M.property
  exact Module.Finite.equiv (leftDualScalarEquiv M.val).symm

def finiteLeftDualModule (M : FiniteModule k A) : FiniteModule k Aᵐᵒᵖ :=
  ⟨leftDualModule M.val, finite_leftDualModule M⟩

theorem finrank_leftDualModule (M : FiniteModule k A) :
    Module.finrank k (leftDualModule (k := k) M.val) = Module.finrank k M.val := by
  let : Module.Finite k M.val := M.property
  rw [(leftDualScalarEquiv M.val).finrank_eq, Subspace.dual_finrank_eq]

def leftDualMap {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    leftDualModule (k := k) N ⟶ leftDualModule (k := k) M := by
  letI := leftDualModuleStructure (k := k) N
  letI := leftDualModuleStructure (k := k) M
  exact ModuleCat.ofHom {
    toFun := fun φ => φ.comp (f.hom.restrictScalars k)
    map_add' := by intro φ ψ; rfl
    map_smul' := by
      intro a φ
      ext x
      change φ (a.unop • f.hom x) = φ (f.hom (a.unop • x))
      rw [f.hom.map_smul]
  }

theorem leftDualMap_id (M : ModuleCat.{max u v} A) :
    leftDualMap (k := k) (𝟙 M) = 𝟙 (leftDualModule (k := k) M) := by
  apply ModuleCat.hom_ext
  ext φ
  rfl

theorem leftDualMap_comp {M N L : ModuleCat.{max u v} A} (f : M ⟶ N) (g : N ⟶ L) :
    leftDualMap (k := k) (f ≫ g) = leftDualMap g ≫ leftDualMap f := by
  apply ModuleCat.hom_ext
  ext φ
  rfl

/-- Finite-dimensional reflexivity, including both changes from native
vector-space scalars to the bundled module scalars. -/
noncomputable def doubleDualScalarEquiv (M : FiniteModule k A) :
    M.val ≃ₗ[k] rightDualModule (k := k) (leftDualModule (k := k) M.val) := by
  let : Module.Finite k M.val := M.property
  exact (Module.evalEquiv k M.val).trans
    ((leftDualScalarEquiv M.val).dualMap.trans
      (rightDualScalarEquiv (leftDualModule M.val)).symm)

/-- Evaluation is an algebra-module equivalence, not just an equivalence
of underlying finite-dimensional vector spaces. -/
noncomputable def doubleDualModuleEquiv (M : FiniteModule k A) :
    M.val ≃ₗ[A] rightDualModule (k := k) (leftDualModule (k := k) M.val) where
  toEquiv := (doubleDualScalarEquiv M).toEquiv
  map_add' := (doubleDualScalarEquiv M).map_add
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro φ
    rfl

noncomputable def doubleDualModuleIso (M : FiniteModule k A) :
    M.val ≅ rightDualModule (k := k) (leftDualModule (k := k) M.val) :=
  (doubleDualModuleEquiv M).toModuleIso

/-- Naturality of the module-valued evaluation isomorphism. -/
theorem doubleDualModuleIso_naturality {M N : FiniteModule k A} (f : M.val ⟶ N.val) :
    f ≫ (doubleDualModuleIso N).hom =
      (doubleDualModuleIso M).hom ≫ rightDualMap (leftDualMap (k := k) f) := by
  apply ModuleCat.hom_ext
  ext x
  rfl

noncomputable def rightDoubleDualScalarEquiv (N : FiniteModule k Aᵐᵒᵖ) :
    N.val ≃ₗ[k] leftDualModule (k := k) (rightDualModule (k := k) N.val) := by
  let : Module.Finite k N.val := N.property
  exact (Module.evalEquiv k N.val).trans
    ((rightDualScalarEquiv N.val).dualMap.trans
      (leftDualScalarEquiv (rightDualModule N.val)).symm)

noncomputable def rightDoubleDualModuleEquiv (N : FiniteModule k Aᵐᵒᵖ) :
    N.val ≃ₗ[Aᵐᵒᵖ] leftDualModule (k := k) (rightDualModule (k := k) N.val) where
  toEquiv := (rightDoubleDualScalarEquiv N).toEquiv
  map_add' := (rightDoubleDualScalarEquiv N).map_add
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro φ
    rfl

noncomputable def rightDoubleDualModuleIso (N : FiniteModule k Aᵐᵒᵖ) :
    N.val ≅ leftDualModule (k := k) (rightDualModule (k := k) N.val) :=
  (rightDoubleDualModuleEquiv N).toModuleIso

theorem rightDoubleDualModuleIso_naturality {M N : FiniteModule k Aᵐᵒᵖ}
    (f : M.val ⟶ N.val) :
    f ≫ (rightDoubleDualModuleIso N).hom =
      (rightDoubleDualModuleIso M).hom ≫ leftDualMap (rightDualMap (k := k) f) := by
  apply ModuleCat.hom_ext
  ext x
  rfl

theorem leftDualMap_injective (M N : FiniteModule k A) :
    Function.Injective (leftDualMap (k := k) (N := N.val) (M := M.val)) := by
  intro f g h
  apply (cancel_mono (doubleDualModuleIso N).hom).mp
  rw [doubleDualModuleIso_naturality, doubleDualModuleIso_naturality, h]

theorem rightDualMap_injective (M N : FiniteModule k Aᵐᵒᵖ) :
    Function.Injective (rightDualMap (k := k) (N := M.val) (M := N.val)) := by
  intro f g h
  apply (cancel_mono (rightDoubleDualModuleIso N).hom).mp
  rw [rightDoubleDualModuleIso_naturality, rightDoubleDualModuleIso_naturality, h]

end C3PerfectField
