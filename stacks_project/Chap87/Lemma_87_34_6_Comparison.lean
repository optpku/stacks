module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.Comparison
public import stacks_project.Chap87.Lemma_87_34_6_Over

/-! # Class-based compatibility for the étale comparison

These specializations retain the legacy reduction interface used by the affine comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [RX : Reduction X]

/-- The identity square on the reduction inclusion commutes. -/
theorem reductionι_id_comp :
    𝟙 (reduction X).functorOfPoints ≫ reductionι X = reductionι X ≫ 𝟙 X := by
  simp only [Category.id_comp, Category.comp_id]

/-- Extension gives a functor from the reduction's étale site to the formal étale slice. -/
abbrev ofSpacesEtale : AlgebraicSpace.spacesEtaleSite (reduction X) ⥤ EtaleOver X :=
  ReductionData.ofSpacesEtale RX.toReductionData

/-- The extension presheaf of an algebraic space étale over the reduction. -/
abbrev extensionAlong (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    (Over S)ᵒᵖ ⥤ Type u :=
  (ofSpacesEtale.obj V).obj.left

/-- Projection of the extension presheaf to the formal space. -/
abbrev extensionHom (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    extensionAlong V ⟶ X :=
  (ofSpacesEtale.obj V).obj.hom

/-- A morphism over the reduction acts by postcomposition on extension points. -/
def extensionAlongMap {V W : AlgebraicSpace.spacesEtaleSite (reduction X)}
    (f : V ⟶ W) : extensionAlong V ⟶ extensionAlong W :=
  ReductionData.extensionAlongMap RX.toReductionData f

/-- Pullback to the reduction gives the forward comparison functor. -/
def toSpacesEtale : EtaleOver X ⥤ AlgebraicSpace.spacesEtaleSite (reduction X) :=
  ReductionData.toSpacesEtale RX.toReductionData

/-- The unit comparison on the underlying presheaves. -/
def unitHom (U : EtaleOver X) :
    U.obj.left ⟶ extensionAlong (toSpacesEtale.obj U) :=
  ReductionData.unitHom RX.toReductionData U

/-- The inverse unit comparison on the underlying presheaves. -/
def unitInv (U : EtaleOver X) :
    extensionAlong (toSpacesEtale.obj U) ⟶ U.obj.left :=
  ReductionData.unitInv RX.toReductionData U

/-- The counit comparison on the underlying algebraic spaces. -/
def counitHom (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    reductionAlong (extensionHom V) ⟶ V.left :=
  ReductionData.counitHom RX.toReductionData V

/-- The inverse counit comparison on the underlying algebraic spaces. -/
def counitInv (V : AlgebraicSpace.spacesEtaleSite (reduction X)) :
    V.left ⟶ reductionAlong (extensionHom V) :=
  ReductionData.counitInv RX.toReductionData V

end AlgebraicGeometry.FormalAlgebraicSpace
