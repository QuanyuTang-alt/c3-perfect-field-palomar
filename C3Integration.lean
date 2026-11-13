module

public import C3PerfectField.AffineCokernelComponents
public import C3PerfectField.PerfectFieldReduction
public import C3KroneckerEmbedding
public import LargeIndecomposable.MainTheorems
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
Assembly of the actual Kronecker embedding with the C3 affine-cokernel
component argument. Both indecomposability notions and representation type
are connected by proofs, not by new assumptions of the main theorem.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace C3PerfectField
open CategoryTheory Limits
open scoped ModuleCat TensorProduct
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Internal submodule and categorical indecomposability denote the same object. -/
theorem indecomposable_iff_largeIndecomposable (M : ModuleCat.{u} A) :
    Indecomposable M ↔ LargeIndecomposable.Statement.IsIndecomposable A M := by
  rw [TauCeti.indecomposable_iff_idempotent_eq_zero_or_id,
    LargeIndecomposable.Reduction.isIndecomposable_iff]

/-- An upstream finite list would make the actual C3 isomorphism quotient finite. -/
theorem not_representationFinite_of_infiniteRepresentationType [FiniteDimensional k A]
    (hA : InfiniteRepresentationType k A) :
    ¬ LargeIndecomposable.Statement.IsRepresentationFinite A := by
  intro hfin
  obtain ⟨n, B, hB⟩ := hfin
  have hM (x : ARVertex k A) : Module.Finite k x.out.obj := x.out.val.property
  let cls : ARVertex k A → Fin n := fun x =>
    letI := hM x
    letI : Module.Finite A x.out.obj := Module.Finite.of_restrictScalars_finite k A _
    Classical.choose (hB x.out.obj
      ((indecomposable_iff_largeIndecomposable x.out.obj).mp x.out.property))
  have hcover (x : ARVertex k A) : Nonempty (x.out.obj ≃ₗ[A] B (cls x)) := by
    letI := hM x
    letI : Module.Finite A x.out.obj := Module.Finite.of_restrictScalars_finite k A _
    exact Classical.choose_spec (hB x.out.obj
      ((indecomposable_iff_largeIndecomposable x.out.obj).mp x.out.property))
  have hinj : Function.Injective cls := by
    intro x y hxy
    obtain ⟨ex⟩ := hcover x
    obtain ⟨ey⟩ := hcover y
    have ei : Nonempty (x.out.obj ≅ y.out.obj) :=
      ⟨ex.toModuleIso ≪≫ eqToIso (congrArg B hxy) ≪≫ ey.toModuleIso.symm⟩
    have hh : (Quotient.mk _ x.out : ARVertex k A) = Quotient.mk _ y.out := Quotient.sound ei
    simpa only [Quotient.out_eq] using hh
  let : Finite (ARVertex k A) := Finite.of_injective cls hinj
  exact (not_finite_iff_infinite.mpr hA) inferInstance

/-- The algebraically closed case, using an actual unconditionally proved
representation embedding and the explicit regular-module presentation. -/
theorem infinite_arComponents_algebraicallyClosed [FiniteDimensional k A] [IsAlgClosed k]
    (hA : InfiniteRepresentationType k A) : Infinite (ARGraph k A).ConnectedComponent := by
  obtain ⟨F, hF, _, hfinite, _⟩ := LargeIndecomposable.theoremA k A
    (not_representationFinite_of_infiniteRepresentationType hA)
  let P := F.obj (C3Kronecker.simpleTarget k)
  let Q := F.obj (C3Kronecker.projectivePair k)
  have hP : Module.Finite k P := hfinite _ C3Kronecker.presentation_finite.1
  have hQ : Module.Finite k Q := hfinite _ C3Kronecker.presentation_finite.2
  let := hP
  let := hQ
  let f : P ⟶ Q := F.map (C3Kronecker.relation (0 : k))
  let g : P ⟶ Q := F.map C3Kronecker.relationDirection
  have hind (lambda : k) : Indecomposable (cokernel (f - lambda • g)) := by
    have hi := (indecomposable_iff_largeIndecomposable (F.obj (C3Kronecker.regular lambda))).mpr
      (C3Kronecker.imageRegular_indecomposable F hF lambda)
    exact hi.of_iso (C3Kronecker.imageRegularCokernelIso F hF lambda).symm
  have hreflect (lambda mu : k)
      (he : Nonempty (cokernel (f - lambda • g) ≅ cokernel (f - mu • g))) : lambda = mu := by
    obtain ⟨e⟩ := he
    exact C3Kronecker.imageRegular_parameter F hF
      ((C3Kronecker.imageRegularCokernelIso F hF lambda).symm ≪≫ e ≪≫
        C3Kronecker.imageRegularCokernelIso F hF mu)
  exact infinite_arComponents_of_injective_affineCokernelFamily f g hind hreflect

/-- Over a perfect field, every finite-dimensional algebra of infinite
representation type has infinitely many connected Auslander--Reiten components. -/
theorem mainTheorem (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [PerfectField k] [FiniteDimensional k A] : MainStatement k A := by
  intro hA
  exact infinite_arComponents_of_scalarExtension (k := k) (K := AlgebraicClosure k)
    (infinite_arComponents_algebraicallyClosed (infiniteRepresentationType_scalarExtension hA))

end C3PerfectField
