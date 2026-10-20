module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import ReasLib.CategoryTheory.Sites.Point.Fiber.Exactness
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
variable {F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)}

/- Lemma 66.19.8 -/
@[stacks 04K1] #check
  (CategoryTheory.GrothendieckTopology.Point.presheafFiber_exact
    (Φ := toSmallEtalePoint xbar) (A := AddCommGrpCat.{u + 1}) :
      exactFunctor
        ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) AddCommGrpCat.{u + 1}
        ((toSmallEtalePoint xbar).presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1}))

#check
  (CategoryTheory.GrothendieckTopology.Point.W_isInvertedBy_presheafFiber
    (Φ := toSmallEtalePoint xbar) (A := Type (u + 1))
    (CategoryTheory.toSheafify (smallEtaleTopology X) F)
    ((smallEtaleTopology X).W_toSheafify F) :
      IsIso ((toSmallEtalePoint xbar).presheafFiber.map
        (CategoryTheory.toSheafify (smallEtaleTopology X) F)))

#check
  (CategoryTheory.GrothendieckTopology.Point.sheafFiber_exact
    (Φ := toSmallEtalePoint xbar) (A := AddCommGrpCat.{u + 1}) :
      exactFunctor
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) AddCommGrpCat.{u + 1}
        ((toSmallEtalePoint xbar).sheafFiber :
          Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
            AddCommGrpCat.{u + 1}))

#check
  (CategoryTheory.GrothendieckTopology.Point.presheafFiber_exact
    (Φ := toSmallEtalePoint xbar) (A := Type (u + 1)) :
      exactFunctor
        ((smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) (Type (u + 1))
        ((toSmallEtalePoint xbar).presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)))

#check
  (CategoryTheory.GrothendieckTopology.Point.sheafFiber_exact
    (Φ := toSmallEtalePoint xbar) (A := Type (u + 1)) :
      exactFunctor
        (Sheaf (smallEtaleTopology X) (Type (u + 1))) (Type (u + 1))
        ((toSmallEtalePoint xbar).sheafFiber :
          Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1)))

#check (((toSmallEtalePoint xbar).skyscraperPresheafAdjunction (A := Type (u + 1))
    ).leftAdjoint_preservesColimits :
      PreservesColimits
        ((toSmallEtalePoint xbar).presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)))

#check (((toSmallEtalePoint xbar).skyscraperSheafAdjunction (A := Type (u + 1))
    ).leftAdjoint_preservesColimits :
      PreservesColimits
        ((toSmallEtalePoint xbar).sheafFiber :
          Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1)))

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
