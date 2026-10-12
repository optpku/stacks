/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.GeometricGenus
import StacksCheckRecall

universe u

/- Definition 53.11.1: the geometric genus of a geometrically irreducible curve is the genus
of any smooth projective model after a possible extension of the ground field. -/
@[stacks 0BYF] #check
  (AlgebraicGeometry.Curve.geometricGenus :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.Curve X] [AlgebraicGeometry.GeometricallyIrreducible X.hom], ℕ)
