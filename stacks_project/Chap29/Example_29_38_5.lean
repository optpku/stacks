/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.WeightedDoubleCover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-!
# Example 29.38.5

The reusable owner constructs a finite weighted double cover of the projective line, its
canonical twists, and the obstruction to relative very ampleness in degrees below the weight of
the square-root generator.
-/

/- Example 29.38.5: for the weighted double cover with square-root generator of positive degree
`d`, relative very ampleness of the canonical twist of index `n` implies `d ≤ n`. -/
@[stacks 01VP] #check
  (AlgebraicGeometry.Proj.WeightedDoubleCover.le_of_twist_relativelyVeryAmple :
    ∀ (k : Type u) [Field k] [Infinite k] (d : ℕ+)
      (lam : Fin (2 * (d : ℕ)) → kˣ) (n : ℤ),
      RelativelyVeryAmple
        (AlgebraicGeometry.Proj.WeightedDoubleCover.toSpec k d
          (fun i => (lam i : k)))
        (AlgebraicGeometry.Proj.WeightedDoubleCover.twist k d
          (fun i => (lam i : k)) n) →
        (d : ℤ) ≤ n)

#check
  (AlgebraicGeometry.Proj.WeightedDoubleCover.instIsAmpleTwistOne :
    ∀ (k : Type u) [CommRing k] (d : ℕ+)
      (lam : Fin (2 * (d : ℕ)) → k),
      Scheme.Modules.IsAmple
        (AlgebraicGeometry.Proj.WeightedDoubleCover.twist k d lam 1))

#check
  (AlgebraicGeometry.Proj.WeightedDoubleCover.binaryTwistSection_bijective_of_lt :
    ∀ (k : Type u) [CommRing k] (d : ℕ+)
      (lam : Fin (2 * (d : ℕ)) → k) {n : ℕ},
      n < (d : ℕ) →
        Function.Bijective
          (AlgebraicGeometry.Proj.WeightedDoubleCover.binaryTwistSection k d lam n))
