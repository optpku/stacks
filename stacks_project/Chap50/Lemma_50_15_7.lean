module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.Smooth

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 50.15.7 -/
@[stacks 0FMY]
#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.isDefined_of_smooth :
  ∀ {S T X Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) (i : Y ⟶ X)
    [AlgebraicGeometry.IsEffectiveCartierDivisor i]
    [AlgebraicGeometry.Smooth f]
    [AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.comp i f)],
    AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined (f ≫ g) i)
