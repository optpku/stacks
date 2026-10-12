/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Gonality

/-! Compatibility surface for the reusable projective-curve gonality API. -/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/- The gonality of a projective curve is a natural number. -/
#check (AlgebraicGeometry.Curve.gonality :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [Projective X.hom], ℕ)

end AlgebraicGeometry.Curve
