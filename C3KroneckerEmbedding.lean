module

public import C3KroneckerPresentation
public import LargeIndecomposable.Modules.KrullSchmidt.IndecomposableFullyFaithful
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Exact embeddings carry the literal regular presentation to an actual
finite-dimensional affine cokernel family. This does not assume equivariance
of the embedding under arbitrary field automorphisms. -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace C3Kronecker
open CategoryTheory Limits
open LargeIndecomposable LargeIndecomposable.Statement
open scoped ModuleCat
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- The parameter coefficient of the actual relation map. -/
abbrev relationDirection : simpleTarget k ⟶ projectivePair k :=
  ObjectProperty.homMk (Kron.homMk 0
    (ModuleCat.ofHom (LinearMap.inl k k k))
    (by ext x; cases x; simp) (by ext x; cases x; simp))

/-- Cokernel isomorphism from a literal exact, surjective pair of module maps. -/
def cokernelIsoOfExactSurjective {P Q R : ModuleCat.{u} A} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : LinearMap.range f.hom = LinearMap.ker g.hom) (hg : Function.Surjective g.hom) :
    cokernel f ≅ R :=
  ModuleCat.cokernelIsoRangeQuotient f ≪≫
    ((Submodule.quotEquivOfEq _ _ h).trans
      (LinearMap.quotKerEquivOfSurjective g.hom hg)).toModuleIso

/-- The image of the regular module is the actual cokernel of the affine relation. -/
def imageRegularCokernelIso (F : D k ⥤ ModuleCat.{u} A)
    (hF : IsRepresentationEmbedding F) (lambda : k) :
    cokernel (F.map (relation (0 : k)) - lambda • F.map relationDirection) ≅
      F.obj (regular lambda) := by
  let := hF.1
  let := hF.2.1
  obtain ⟨_, hsurj, hexact⟩ := hF.2.2.1 _ _ _ (relation lambda) (projection lambda)
    (presentation_shortExact lambda)
  have hmap : F.map (relation lambda) =
      F.map (relation (0 : k)) - lambda • F.map relationDirection := by
    rw [relation_affine, F.map_sub, F.map_smul]
  exact cokernelIsoOfEq hmap.symm ≪≫
    cokernelIsoOfExactSurjective (F.map (relation lambda)) (F.map (projection lambda)) hexact hsurj

/-- Isomorphisms in the image family reflect the actual scalar parameter. -/
theorem imageRegular_parameter (F : D k ⥤ ModuleCat.{u} A)
    (hF : IsRepresentationEmbedding F) {lambda mu : k}
    (e : F.obj (regular lambda) ≅ F.obj (regular mu)) : lambda = mu := by
  obtain ⟨i⟩ := hF.2.2.2.2 _ _ ⟨e⟩
  exact regular_iso_parameter i

/-- Actual images of the literal regular family are indecomposable. -/
theorem imageRegular_indecomposable (F : D k ⥤ ModuleCat.{u} A)
    (hF : IsRepresentationEmbedding F) (lambda : k) :
    IsIndecomposable A (F.obj (regular lambda)) :=
  hF.2.2.2.1 _ (regular_indecomposable lambda)

end C3Kronecker
