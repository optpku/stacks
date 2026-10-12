/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Splitting
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Situation 79.15.3 (Splitting): standing hypotheses on a pointed groupoid scheme
`(U, R, s, t, c)` over a scheme `S` at an object point. -/
@[stacks 0DTB] #check (AlgebraicGeometry.GroupoidScheme.SplittingHypotheses :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    (G : AlgebraicGeometry.GroupoidScheme S) → G.U.left → Prop)

/-- The splitting hypotheses on a pointed groupoid scheme, carried as a fact for
source-facing typeclass binders. -/
abbrev IsSplittingSituation {S : Scheme.{u}} (G : GroupoidScheme S) (point : G.U.left) : Prop :=
  Fact (SplittingHypotheses G point)

end AlgebraicGeometry.GroupoidScheme
