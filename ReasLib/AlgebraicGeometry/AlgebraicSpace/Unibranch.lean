module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Unibranch

/-!
# Unibranch decent algebraic spaces

A decent algebraic space is unibranch at a point when its henselian local ring
there is unibranch, and unibranch when this holds at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]

/-- A decent algebraic space `X` is unibranch at a point `x` when the henselian
local ring of `X` at `x` is unibranch. -/
@[stacks 0DQ7]
abbrev isUnibranchAt (x : Points X) : Prop :=
  _root_.IsUnibranch (henselianLocalRing X x)

/-- A decent algebraic space is unibranch when it is unibranch at every point. -/
@[stacks 0DQ7]
abbrev isUnibranch : Prop :=
  ∀ x : Points X, X.isUnibranchAt x

/-- Unibranchness at a point of a decent algebraic space is unibranchness of the
henselian local ring. -/
theorem isUnibranchAt_iff (x : Points X) :
    X.isUnibranchAt x ↔ _root_.IsUnibranch (henselianLocalRing X x) :=
  sorry

/-- Unibranchness at a point is equivalent to uniqueness of a minimal prime of
the henselian local ring. -/
theorem isUnibranchAt_iff_uniqueMinimalPrime (x : Points X) :
    X.isUnibranchAt x ↔
      ∃! p : Ideal (henselianLocalRing X x), p ∈ minimalPrimes (henselianLocalRing X x) :=
  sorry

/-- Unibranchness at a point is equivalent to unibranchness of every elementary
étale neighbourhood at its selected point. -/
theorem isUnibranchAt_iff_elementary (x : Points X) :
    X.isUnibranchAt x ↔
      ∀ U : EtaleNeighborhood.Elementary X x, U.obj.scheme.isUnibranchAt U.obj.point :=
  sorry

/-- A decent algebraic space is unibranch exactly when it is unibranch at every
point. -/
theorem isUnibranch_iff : X.isUnibranch ↔ ∀ x : Points X, X.isUnibranchAt x :=
  sorry

end

/-- A scheme over `S`, viewed as an algebraic space, is unibranch at a point if
and only if the corresponding scheme point is unibranch. -/
theorem isUnibranchAt_ofOver_iff {S : Scheme.{u}} (T : Over S) (x : T.left) :
    isUnibranchAt (ofOver T) (ofOver.pointsEquiv T x) ↔ T.left.isUnibranchAt x :=
  sorry

/-- A scheme over `S`, viewed as an algebraic space, is unibranch if and only if
the underlying scheme is unibranch. -/
theorem isUnibranch_ofOver_iff {S : Scheme.{u}} (T : Over S) :
    isUnibranch (ofOver T) ↔ T.left.isUnibranch :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
