module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Relative

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

#check
  (@AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfectOver :
    {X S : RingedSpace.{u}} → (f : X ⟶ S) →
      RingedSpace.ModuleDerived X → Prop)
