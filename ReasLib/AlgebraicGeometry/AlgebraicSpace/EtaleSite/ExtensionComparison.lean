module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafAdjunction

/-! # Comparing small-chart extension with extension on all scheme charts -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleTopos

variable {S : Scheme.{u}}

/-- Each actual sheaf has the specified limit on all scheme charts. -/
instance fullChartPointwise (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) (Type u)) :
    (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension Q.obj :=
  fun W ↦ allChartHasLimit X Q W.unop

/-- Right Kan extension of this sheaf, constructed from its actual chart limits. -/
def fullChartExtension (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) (Type u)) : (spacesEtaleSite X)ᵒᵖ ⥤ Type u :=
  Functor.pointwiseRightKanExtension (smallEtaleToSpaces X).op Q.obj

/-- The actual pointwise Kan counit evaluates a section on a scheme chart. -/
def fullChartCounit (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) (Type u)) :
    (smallEtaleToSpaces X).op ⋙ fullChartExtension X Q ⟶ Q.obj :=
  Functor.pointwiseRightKanExtensionCounit (smallEtaleToSpaces X).op Q.obj

/-- The small-chart extension and extension on all scheme charts have canonically
isomorphic section types, using their specified limit cones. -/
def extensionEvaluationIso (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) (Type u)) (W : spacesEtaleSite X) :
    ((extension X).obj Q).obj.obj (op W) ≅
      (fullChartExtension X Q).obj (op W) :=
  (allChartIsLimit X Q W).conePointUniqueUpToIso (limit.isLimit _)

/-- The comparison recovers evaluation on each scheme chart by the Kan counit. -/
@[reassoc]
theorem extensionEvaluationIso_hom_evaluation (X : AlgebraicSpace S)
    (Q : Sheaf (smallEtaleTopology X) (Type u)) {W : spacesEtaleSite X}
    {U : smallEtaleSite X} (a : (smallEtaleToSpaces X).obj U ⟶ W) :
    (extensionEvaluationIso X Q W).hom ≫
        (fullChartExtension X Q).map a.op ≫
        (fullChartCounit X Q).app (op U) =
      extensionEvaluation X Q a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleTopos
