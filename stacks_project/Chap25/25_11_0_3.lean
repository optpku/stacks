/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Intersection
import StacksCheckRecall

/-!
Equation 25.11.0.3 is the reusable matching-index and finite-intersection cover condition for
simplicial open hypercoverings.
-/

@[expose] public section

open TopologicalSpace

universe u v w

variable {X : Type u} [TopologicalSpace X] {n : ℕ} {Iₙ : Type v} {Iₙ₁ : Type w}
variable (d : Fin (n + 2) → Iₙ₁ → Iₙ) (Uₙ : Iₙ → Opens X) (Uₙ₁ : Iₙ₁ → Opens X)
variable (compatible : (Fin (n + 2) → Iₙ) → Prop)

/- 25.11.0.3: matching degree-`n + 1` opens cover every prescribed finite intersection of
degree-`n` opens. The canonical owner is `SSet.OpenHypercovering.Intersection`. -/
@[stacks 01H4]
#check (SSet.OpenHypercovering.Intersection d Uₙ Uₙ₁ compatible : Prop)

/- The matching-index subtype used by the source condition is
`SSet.OpenHypercovering.MatchingIndices`. -/
#check @SSet.OpenHypercovering.MatchingIndices

/- The source's pairwise `n = 0` specialization is provided by
`SSet.OpenHypercovering.PairwiseIntersection`. -/
#check SSet.OpenHypercovering.PairwiseIntersection
