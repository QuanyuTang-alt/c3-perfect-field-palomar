module

public import C3PerfectField.HomDimensions

/-!
Finite minimal projective presentations for the modules in the target
statement, and the kernel and hom-space estimates in `lem:transpose-bound`.
The full module-valued transpose and the almost split existence theorem
are not supplied by this file.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- The actual kernel of an `A`-module homomorphism as a bundled module. -/
def moduleKernel {P X : FiniteModule k A} (p : P.val ⟶ X.val) :
    ModuleCat.{max u v} A :=
  ModuleCat.of A p.hom.ker

def moduleKernelInclusion {P X : FiniteModule k A} (p : P.val ⟶ X.val) :
    moduleKernel p ⟶ P.val :=
  ModuleCat.ofHom p.hom.ker.subtype

theorem moduleKernelInclusion_injective {P X : FiniteModule k A}
    (p : P.val ⟶ X.val) : Function.Injective (moduleKernelInclusion p).hom :=
  Subtype.val_injective

theorem finite_moduleKernel {P X : FiniteModule k A} (p : P.val ⟶ X.val) :
    Module.Finite k (moduleKernel p) := by
  let : Module.Finite k P.val := P.property
  exact FiniteDimensional.of_injective
    ((moduleKernelInclusion p).hom.restrictScalars k)
    (moduleKernelInclusion_injective p)

/-- The kernel carries its proved finite-dimensionality. -/
def finiteKernelModule {P X : FiniteModule k A} (p : P.val ⟶ X.val) :
    FiniteModule k A :=
  ⟨moduleKernel p, finite_moduleKernel p⟩

theorem finrank_moduleKernel_le {P X : FiniteModule k A} (p : P.val ⟶ X.val) :
    Module.finrank k (moduleKernel p) ≤ Module.finrank k P.val := by
  let : Module.Finite k P.val := P.property
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (moduleKernelInclusion p).hom.restrictScalars k)
    (moduleKernelInclusion_injective p)

theorem moduleKernelInclusion_comp {P X : FiniteModule k A} (p : P.val ⟶ X.val) :
    moduleKernelInclusion p ≫ p = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact x.property

/-- The two projective covers in the manuscript's chosen minimal
projective presentation. The first syzygy is the actual kernel, and the
second projective module covers that kernel. -/
structure MinimalProjectivePresentation (X : FiniteModule k A) where
  P₀ : FiniteModule k A
  p₀ : P₀.val ⟶ X.val
  cover₀ : IsProjectiveCover (k := k) p₀
  P₁ : FiniteModule k A
  p₁ : P₁.val ⟶ (finiteKernelModule p₀).val
  cover₁ : IsProjectiveCover (k := k) p₁

theorem exists_minimalProjectivePresentation [FiniteDimensional k A]
    (X : FiniteModule k A) : Nonempty (MinimalProjectivePresentation X) := by
  obtain ⟨P₀, p₀, hp₀⟩ := exists_projectiveCover X
  obtain ⟨P₁, p₁, hp₁⟩ := exists_projectiveCover (finiteKernelModule p₀)
  exact ⟨⟨P₀, p₀, hp₀, P₁, p₁, hp₁⟩⟩

namespace MinimalProjectivePresentation

variable {X : FiniteModule k A} (T : MinimalProjectivePresentation X)

def differential : T.P₁.val ⟶ T.P₀.val :=
  T.p₁ ≫ moduleKernelInclusion T.p₀

theorem differential_comp : T.differential ≫ T.p₀ = 0 := by
  calc
    T.differential ≫ T.p₀ =
        T.p₁ ≫ (moduleKernelInclusion T.p₀ ≫ T.p₀) :=
      Category.assoc _ _ _
    _ = T.p₁ ≫ 0 := congrArg (fun f => T.p₁ ≫ f) (moduleKernelInclusion_comp T.p₀)
    _ = 0 := Limits.comp_zero

/-- The presentation is exact at `P₀`: the range of its differential is
the actual kernel, rather than merely a submodule of that kernel. -/
theorem range_differential :
    LinearMap.range T.differential.hom = LinearMap.ker T.p₀.hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp T.differential_comp) y
  · intro hx
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective T.p₁).mp T.cover₁.2.1 ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem finrank_syzygy_le [FiniteDimensional k A] :
    Module.finrank k (moduleKernel T.p₀) ≤
      Module.finrank k A * Module.finrank k X.val :=
  (finrank_moduleKernel_le T.p₀).trans (finrank_projectiveCover_le T.p₀ T.cover₀)

/-- The hom-space estimate before taking the transpose quotient. -/
theorem finrank_hom_P₁_le [FiniteDimensional k A] (V : FiniteModule k A) :
    Module.finrank k (T.P₁.val ⟶ V.val) ≤
      Module.finrank k V.val * Module.finrank k A * Module.finrank k X.val := by
  have h := (finrank_hom_projectiveCover_le T.p₁ T.cover₁ V).trans
    (Nat.mul_le_mul_right (Module.finrank k V.val) T.finrank_syzygy_le)
  simpa only [finiteKernelModule, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

end MinimalProjectivePresentation
end C3PerfectField
