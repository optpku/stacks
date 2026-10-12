/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
