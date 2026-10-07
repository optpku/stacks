module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.GeometricallyUnibranch

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.37.1: a locally finite type morphism to an integral scheme that is
geometrically unibranch at the image of `x` is etale at `x` if it is unramified
there and a generization of `x` maps to the generic point. -/
@[stacks 0GS8]
#check (AlgebraicGeometry.Scheme.Hom.UnramifiedAt.etaleAt_of_specializes_genericPoint :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsIntegral Y] [AlgebraicGeometry.LocallyOfFiniteType f]
    (x x' : X),
    Y.isGeometricallyUnibranchAt (f x) → x' ⤳ x →
      f x' = genericPoint Y → f.UnramifiedAt x →
        f.EtaleAt x)
