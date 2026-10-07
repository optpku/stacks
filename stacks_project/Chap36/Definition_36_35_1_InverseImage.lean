module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

#check
  (@AlgebraicGeometry.RingedSpace.ModuleDerived.relativeRestriction :
    {X S : RingedSpace.{u}} → (f : X ⟶ S) →
      RingedSpace.ModuleDerived X ⥤
        RingedSpace.ModuleDerived (RingedSpace.Hom.inverseImageBase f))
