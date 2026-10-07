module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Unibranch

/-!
# Unibranch schemes at a point

This leaf gives the stalkwise scheme formulation of unibranch and
geometrically unibranch local rings.  The ring-level reduction-normalization
owner remains in `ReasLib.RingTheory.LocalRing.Unibranch`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme `X` is unibranch at `x` when its local ring at `x` is unibranch. -/
@[stacks 0BQ2 "unibranch at a scheme point"]
abbrev isUnibranchAt (x : X) : Prop :=
  _root_.IsUnibranch (X.presheaf.stalk x)

/-- The stalkwise characterization of unibranchness at a scheme point. -/
@[simp, stacks 0BQ2 "unibranch at a scheme point iff stalk unibranch"]
theorem isUnibranchAt_iff (x : X) :
    X.isUnibranchAt x ↔ _root_.IsUnibranch (X.presheaf.stalk x) := sorry

/-- Unibranchness at a scheme point supplies unibranchness of its stalk. -/
@[stacks 0BQ2 "unibranch scheme point gives unibranch stalk"]
theorem isUnibranchAt.isUnibranch {x : X}
    (hx : X.isUnibranchAt x) : _root_.IsUnibranch (X.presheaf.stalk x) := sorry

/-- A scheme `X` is geometrically unibranch at `x` when its local ring at
`x` is geometrically unibranch. -/
@[stacks 0BQ2 "geometrically unibranch at a scheme point"]
abbrev isGeometricallyUnibranchAt (x : X) : Prop :=
  _root_.IsGeometricallyUnibranch (X.presheaf.stalk x)

/-- The stalkwise characterization of geometric unibranchness at a scheme
point. -/
@[simp, stacks 0BQ2 "geometrically unibranch at a scheme point iff stalk"]
theorem isGeometricallyUnibranchAt_iff (x : X) :
    X.isGeometricallyUnibranchAt x ↔
      _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) := sorry

/-- Geometric unibranchness at a scheme point supplies geometric
unibranchness of its stalk. -/
@[stacks 0BQ2 "geometrically unibranch scheme point gives stalk property"]
theorem isGeometricallyUnibranchAt.isGeometricallyUnibranch {x : X}
    (hx : X.isGeometricallyUnibranchAt x) :
    _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) := sorry

/-- Geometric unibranchness at a scheme point implies unibranchness there. -/
@[stacks 0BQ2 "geometrically unibranch implies unibranch at a scheme point"]
theorem isGeometricallyUnibranchAt.isUnibranchAt {x : X}
    (hx : X.isGeometricallyUnibranchAt x) : X.isUnibranchAt x := sorry

/-- A scheme is unibranch when it is unibranch at every point. -/
@[stacks 0BQ2 "unibranch scheme"]
abbrev isUnibranch : Prop :=
  ∀ x : X, X.isUnibranchAt x

/-- A unibranch scheme is unibranch at each point. -/
@[stacks 0BQ2 "unibranch scheme point readout"]
theorem isUnibranch.isUnibranchAt (hX : X.isUnibranch) (x : X) :
    X.isUnibranchAt x := sorry

/-- Every stalk of a unibranch scheme is unibranch. -/
@[stacks 0BQ2 "unibranch scheme stalk readout"]
theorem isUnibranch.isUnibranch_stalk (hX : X.isUnibranch) (x : X) :
    _root_.IsUnibranch (X.presheaf.stalk x) := sorry

/-- A scheme is unibranch exactly when all of its stalks are unibranch. -/
@[simp, stacks 0BQ2 "unibranch scheme iff all stalks are unibranch"]
theorem isUnibranch_iff :
    X.isUnibranch ↔ ∀ x : X, _root_.IsUnibranch (X.presheaf.stalk x) := sorry

/-- A scheme is geometrically unibranch when it is geometrically unibranch at
every point. -/
@[stacks 0BQ2 "geometrically unibranch scheme"]
abbrev isGeometricallyUnibranch : Prop :=
  ∀ x : X, X.isGeometricallyUnibranchAt x

/-- A geometrically unibranch scheme is geometrically unibranch at each
point. -/
@[stacks 0BQ2 "geometrically unibranch scheme point readout"]
theorem isGeometricallyUnibranch.isGeometricallyUnibranchAt
    (hX : X.isGeometricallyUnibranch) (x : X) :
    X.isGeometricallyUnibranchAt x := sorry

/-- Every stalk of a geometrically unibranch scheme is geometrically
unibranch. -/
@[stacks 0BQ2 "geometrically unibranch scheme stalk readout"]
theorem isGeometricallyUnibranch.isGeometricallyUnibranch_stalk
    (hX : X.isGeometricallyUnibranch) :
    ∀ x : X, _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) := sorry

/-- A scheme is geometrically unibranch exactly when all of its stalks are
geometrically unibranch. -/
@[simp, stacks 0BQ2 "geometrically unibranch scheme iff all stalks"]
theorem isGeometricallyUnibranch_iff :
    X.isGeometricallyUnibranch ↔
      ∀ x : X, _root_.IsGeometricallyUnibranch (X.presheaf.stalk x) := sorry

/-- A geometrically unibranch scheme is unibranch. -/
@[stacks 0BQ2 "geometrically unibranch scheme implies unibranch"]
theorem isGeometricallyUnibranch.isUnibranch
    (hX : X.isGeometricallyUnibranch) : X.isUnibranch := sorry

end AlgebraicGeometry.Scheme
