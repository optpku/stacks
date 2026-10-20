module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 76.52.1: for a scheme `S` and a flat, locally finitely presented morphism
`f : X ⟶ Y` of algebraic spaces over `S`, an object of `D(𝒪_X)` is `Y`-perfect when it is
pseudo-coherent over `𝒪_X` and locally has finite Tor dimension as an object of
`D(f⁻¹𝒪_Y)`. -/
@[stacks 0DKN] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicSpace.Flat f] [AlgebraicSpace.LocallyOfFinitePresentation f],
      ModuleDerived X → Prop)
