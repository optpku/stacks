/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.RingTheory.Normal.Local

/-!
# Normal schemes are geometrically unibranch

This leaf relates normality of a scheme to geometric unibranchness.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A scheme normal at a point is geometrically unibranch at that point. -/
theorem isNormalAt.isGeometricallyUnibranchAt {x : X}
    (hx : X.isNormalAt x) :
    X.isGeometricallyUnibranchAt x := sorry

/-- A normal scheme is geometrically unibranch. -/
theorem isGeometricallyUnibranch_of_isNormal
    (hX : X.isNormal) :
    X.isGeometricallyUnibranch := fun x ↦
  (Scheme.isNormal.isNormalAt X hX x).isGeometricallyUnibranchAt

end AlgebraicGeometry.Scheme
