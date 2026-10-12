/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZeroStalk
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology.Point

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} AddCommGrpCat.{u}]
variable [HasProducts.{u} AddCommGrpCat.{u}]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback j).op.HasLeftKanExtension P]
variable [((smallEtalePullback j).sheafPushforwardContinuous AddCommGrpCat.{u}
    X.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]

/- Proposition 59.70.3 -/
@[stacks 03S5] #check
  (AlgebraicGeometry.Scheme.abelianExtensionByZero_stalkIso j :
    ∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
      (xbar : GeometricPoint X)
      [∀ u : GeometricPoint.Fiber j xbar,
        InitiallySmall
          ((smallEtalePullback j ⋙
            (GeometricPoint.toSmallEtalePoint u.point).fiber).Elements)],
      IsIso (abelianExtensionByZero_stalkComparison j F xbar))

#check
  (abelianExtensionByZero_exact j :
    exactFunctor
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (abelianExtensionByZero j))

end AlgebraicGeometry.Scheme
