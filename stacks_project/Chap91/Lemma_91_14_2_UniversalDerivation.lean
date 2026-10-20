module
public import stacks_project.Chap91.Lemma_91_14_2_GeometricNLComparison
public import stacks_project.Chap76.Lemma_76_17_1_Difference
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Hom
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Hom.GeometricNL
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The actual degree-zero cokernel of the geometric naïve cotangent complex. -/
abbrev omega := cokernel (cotangentDifferential f)

/-- A section x is sent to the class of its polynomial differential d[X_x]. -/
def sectionDifferential (U : (smallEtaleSite X)ᵒᵖ)
    (x : (commStructureSheaf X).obj.obj U) : (omega f).val.obj U :=
  -- Local instance justification (noncanonical choice): use the coefficient algebra specified by this morphism f and site object U.
  letI := inverseImageAlgebra f U
  (cokernel.π (cotangentDifferential f)).val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureSheaf X).obj)).unit.app (cotangentSpacePresheaf f)).app U
        ((presentation f U).cotangentSpaceBasis x))

/-- The source Kähler derivation is constructed on generators in the conormal cokernel. -/
def universalDerivation :
    Hom.Deformation.derivations f (omega f) where
  d := { toFun := sectionDifferential f _, map_zero' := sorry, map_add' := sorry }
  d_mul := sorry
  d_map := sorry
  d_app := sorry

/-- The generator formula, retained independently of the derivation proof obligations. -/
theorem universalDerivation_apply (U : (smallEtaleSite X)ᵒᵖ)
    (x : (commStructureSheaf X).obj.obj U) :
    (universalDerivation f).d (X := U) x = sectionDifferential f U x := rfl

/-- Morphisms out of this cokernel are determined by their values on the actual d[X_x]. -/
theorem universalDerivation_postcomp_injective (G : X.Modules) :
    Function.Injective (fun q : omega f ⟶ G ↦ (universalDerivation f).postcomp q.val) := sorry
end AlgebraicGeometry.AlgebraicSpace.Hom.GeometricNL
