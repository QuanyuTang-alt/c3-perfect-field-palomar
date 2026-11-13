-- Ported for the pinned Lean/Mathlib version with Doubao assistance; original notices retained.
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
The target statement and its representation-theoretic objects.

This file contains definitions, not a proof of `thm:main`. The arrow relation
uses the manuscript's radical criterion and finite sums of radical
factorizations. Neither an abstract graph nor a representation embedding is
accepted as a premise of the target statement.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory
open scoped ModuleCat
open scoped BigOperators

universe u v

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]

/-- Unital left `A`-modules finite-dimensional over the base field. -/
def FiniteModule := {M : ModuleCat.{max u v} A // Module.Finite k M}

/-- Nonzero indecomposable objects of the finite-dimensional module category.
`CategoryTheory.Indecomposable` excludes the zero object. -/
def IndecomposableModule :=
  {M : FiniteModule k A // CategoryTheory.Indecomposable M.val}

namespace IndecomposableModule

variable {k A}

abbrev obj (X : IndecomposableModule k A) : ModuleCat.{max u v} A := X.val.val

/-- The usual module-isomorphism relation. -/
def isoSetoid : Setoid (IndecomposableModule k A) where
  r X Y := Nonempty (X.obj ≅ Y.obj)
  iseqv :=
    ⟨fun X => ⟨Iso.refl X.obj⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

end IndecomposableModule

/-- The actual indecomposable isomorphism classes, not chosen abstract vertices. -/
def ARVertex := Quotient (IndecomposableModule.isoSetoid (k := k) (A := A))

/-- Manuscript Definition `def:radical`, with categorical composition written
in left-to-right order. -/
def IsRadical {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y) : Prop :=
  ∀ g : Y ⟶ X, IsIso (𝟙 X - f ≫ g)

/-- Membership in the categorical radical square: arbitrary finite sums,
factoring through arbitrary finite-dimensional modules. -/
def IsRadicalSquare {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y) : Prop :=
  ∃ (n : ℕ) (W : Fin n → FiniteModule k A)
    (a : ∀ j, X ⟶ (W j).val) (b : ∀ j, (W j).val ⟶ Y),
    (∀ j, IsRadical A (a j) ∧ IsRadical A (b j)) ∧
      f = ∑ j, a j ≫ b j

/-- An arrow on representatives is a nonzero element of radical modulo its
square, expressed by the equivalent membership criterion. -/
def HasARArrow (X Y : IndecomposableModule k A) : Prop :=
  ∃ f : X.obj ⟶ Y.obj, IsRadical A f ∧ ¬IsRadicalSquare k A f

/-- The induced arrow relation on isomorphism classes. The existence of
representatives makes this a definition without making a choice of modules. -/
def ARArrow (x y : ARVertex k A) : Prop :=
  ∃ X Y : IndecomposableModule k A,
    Quotient.mk _ X = x ∧ Quotient.mk _ Y = y ∧ HasARArrow k A X Y

/-- Undirected connectivity of the manuscript's Auslander--Reiten graph.
Loops can be discarded because length-zero paths are allowed. -/
def ARGraph : SimpleGraph (ARVertex k A) where
  Adj x y := x ≠ y ∧ (ARArrow k A x y ∨ ARArrow k A y x)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by simp⟩

/-- Infinite representation type, with isomorphism classes made explicit. -/
def InfiniteRepresentationType : Prop := Infinite (ARVertex k A)

/-- The precise target proposition corresponding to `thm:main`.
The substantive proof is C3PerfectField.mainTheorem in C3Integration. -/
def MainStatement [PerfectField k] [FiniteDimensional k A] : Prop :=
  InfiniteRepresentationType k A → Infinite (ARGraph k A).ConnectedComponent

end C3PerfectField
