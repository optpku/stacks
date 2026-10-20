module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.HigherDirectImage

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Scheme

/-- For an integral normal scheme with separably closed function field, the positive-degree
higher direct images of every constant abelian sheaf along any scheme morphism vanish. -/
theorem higherDirectImage_constantSheaf_isZero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] (hX : X.isNormal)
    [IsSepClosed X.functionField] (M : AddCommGrpCat.{u}) {q : ℕ} (hq : 0 < q)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    IsZero
      (Sheaf.higherDirectImage (smallEtalePullback f)
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M) q :
        Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) := sorry

end AlgebraicGeometry.Scheme
