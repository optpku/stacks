/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch

@[expose] public section

universe u

/- Definition 28.15.1 (1): a scheme is unibranch at a point when its local
ring there is unibranch. -/
@[stacks 0BQ2] #check
  (AlgebraicGeometry.Scheme.isUnibranchAt :
    (X : AlgebraicGeometry.Scheme.{u}) → X → Prop)

/- Definition 28.15.1 (2): a scheme is geometrically unibranch at a point
when its local ring there is geometrically unibranch. -/
@[stacks 0BQ2] #check
  (AlgebraicGeometry.Scheme.isGeometricallyUnibranchAt :
    (X : AlgebraicGeometry.Scheme.{u}) → X → Prop)

/- Definition 28.15.1 (3): a scheme is unibranch when it is unibranch at
every point. -/
@[stacks 0BQ2] #check
  (AlgebraicGeometry.Scheme.isUnibranch :
    AlgebraicGeometry.Scheme.{u} → Prop)

/- Definition 28.15.1 (4): a scheme is geometrically unibranch when it is
geometrically unibranch at every point. -/
@[stacks 0BQ2] #check
  (AlgebraicGeometry.Scheme.isGeometricallyUnibranch :
    AlgebraicGeometry.Scheme.{u} → Prop)
