module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.Transitivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent

universe u

/- Definition 92.26.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. The cotangent complex `L_{X/Y}` of `X` over `Y` is the cotangent
complex of the morphism of ringed topoi `f_small` between the small étale sites of
`X` and `Y` (see Properties of Spaces, Lemma 66.21.3 and Definition 92.22.1). -/
@[stacks 08VD]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangentCochain :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    CochainComplex (AlgebraicGeometry.AlgebraicSpace.Cotangent.CommModules X) ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    DerivedCategory (AlgebraicGeometry.AlgebraicSpace.Cotangent.CommModules X))
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangentCochain_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangentCochain f =
      AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangentCochainObj
        (AlgebraicGeometry.AlgebraicSpace.Cotangent.structureMapLift f))
