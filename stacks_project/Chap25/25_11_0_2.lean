/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Intersection
import StacksCheckRecall

/-!
Equation 25.11.0.2 is the two-face specialization of the reusable matching-index intersection
condition.
-/

@[expose] public section

open TopologicalSpace

universe u v w

variable {X : Type u} [TopologicalSpace X] {I₀ : Type v} {I₁ : Type w}
variable (d₀ d₁ : I₁ → I₀) (U₀ : I₀ → Opens X) (U₁ : I₁ → Opens X)

/- 25.11.0.2: the level-`1` opens matching a pair of level-`0` indices cover their intersection.
The canonical owner is `SSet.OpenHypercovering.PairwiseIntersection`. -/
@[stacks 01H3]
#check (SSet.OpenHypercovering.PairwiseIntersection d₀ d₁ U₀ U₁ : Prop)

/- The source-facing pairwise supremum formula is
`SSet.OpenHypercovering.PairwiseIntersection.inf_eq_iSup`. -/
#check @SSet.OpenHypercovering.PairwiseIntersection.inf_eq_iSup
