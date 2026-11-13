module

public import C3PerfectField.ScalarExtensionPaths
public import C3PerfectField.SummandDescent

/-!
Manuscript `prop:components`. If the actual base AR graph has finitely
many connected components, then the algebraic-closure extension does too.
Every extended indecomposable descends as a summand; lifting a path
then puts it in a component meeting one of finitely many chosen summands.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct Classical

universe u v

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- Finitely many base components give finitely many extended components.
The domain of the final surjection consists of the actual indecomposable
factors of the extensions of finitely many component representatives. -/
theorem finite_arComponents_scalarExtension
    [Finite (ARGraph k A).ConnectedComponent] :
    Finite (ARGraph K (K ⊗[k] A)).ConnectedComponent := by
  classical
  let G := ARGraph k A
  let H := ARGraph K (K ⊗[k] A)
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hex : ∀ c : G.ConnectedComponent, ∃ x, G.connectedComponentMk x = c :=
    fun c => c.ind fun x => ⟨x, rfl⟩
  choose rep hrep using hex
  let M : G.ConnectedComponent → IndecomposableModule k A := fun c => (rep c).out
  have hdecomp (c : G.ConnectedComponent) :
      ∃ (n : ℕ) (P : Fin n → IndecomposableModule K (K ⊗[k] A)),
        Nonempty ((scalarExtensionFiniteModule (L := K) (M c).val).val ≅
          ⨁ fun i => (P i).obj) :=
    exists_indecomposable_biproduct _
  choose n P e using hdecomp
  let e' := fun c => (e c).some
  let f : (Σ c : G.ConnectedComponent, Fin (n c)) → H.ConnectedComponent :=
    fun ci => H.connectedComponentMk (Quotient.mk _ (P ci.1 ci.2))
  apply Finite.of_surjective f
  intro d
  refine d.ind ?_
  intro z
  let N := z.out
  obtain ⟨X, hX⟩ := exists_indecomposable_scalarExtension_summand (k := k) N
  let c := G.connectedComponentMk (Quotient.mk _ X)
  have hpath : G.Reachable (Quotient.mk _ X) (Quotient.mk _ (M c)) := by
    apply SimpleGraph.ConnectedComponent.exact
    rw [Quotient.out_eq]
    exact (hrep c).symm
  obtain ⟨V, hV, hNV⟩ := exists_scalarExtension_path_of_reachable X (M c) hpath N hX
  obtain ⟨i, ⟨ei⟩⟩ := (isIndecomposableSummand_iff_component_iso V _ (P c) (e' c)).mp hV
  refine ⟨⟨c, i⟩, ?_⟩
  change H.connectedComponentMk (Quotient.mk _ (P c i)) = H.connectedComponentMk z
  have heq : (Quotient.mk _ V : ARVertex K (K ⊗[k] A)) = Quotient.mk _ (P c i) :=
    Quotient.sound ⟨ei⟩
  have hn : (Quotient.mk _ N : ARVertex K (K ⊗[k] A)) = z := Quotient.out_eq z
  exact (SimpleGraph.ConnectedComponent.sound (by simpa only [heq, hn] using hNV)).symm

/-- Infinitely many components after algebraic-closure extension force
infinitely many components over the original perfect field. -/
theorem infinite_arComponents_of_scalarExtension
    (h : Infinite (ARGraph K (K ⊗[k] A)).ConnectedComponent) :
    Infinite (ARGraph k A).ConnectedComponent := by
  by_contra hn
  let := not_infinite_iff_finite.mp hn
  let := finite_arComponents_scalarExtension (k := k) (K := K) (A := A)
  exact (not_finite_iff_infinite.mpr h) inferInstance

end

end C3PerfectField
