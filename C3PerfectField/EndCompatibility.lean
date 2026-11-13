module

public import Mathlib.CategoryTheory.Linear.Basic

/-! Compatibility with the older pinned Mathlib: `End X` is definitionally
the hom type in this version. These maps are the identity, preserving the
actual morphism, additive and scalar structures. -/
@[expose] public section
namespace CategoryTheory.End
universe u v w
variable {C : Type u} [Category.{v} C]

@[implicit_reducible]
def homEquiv {X : C} : End X ≃ (X ⟶ X) := Equiv.refl _

@[implicit_reducible]
def linearEquiv {R : Type w} [Semiring R] [Preadditive C] [Linear R C] {X : C} :
    End X ≃ₗ[R] (X ⟶ X) := LinearEquiv.refl R _
end CategoryTheory.End
