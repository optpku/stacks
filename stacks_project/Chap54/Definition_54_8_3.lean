/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap54.Definition_54_8_3_Reduction
public import stacks_project.Chap54.Situation_54_12_1_RationalSingularity

universe u

/- Definition 54.8.3 (1): a two-dimensional local normal Nagata domain defines a rational
singularity when `H¹(X, 𝒪_X)` vanishes for every normal modification `X ⟶ Spec A`. -/
@[stacks 0B4N] #check (@IsRationalSingularity : (A : Type u) → [CommRing A] → Prop)

/- Definition 54.8.3 (2): reduction to rational singularities is possible when the lengths of
`H¹(X, 𝒪_X)` are uniformly bounded over all normal modifications `X ⟶ Spec A`. -/
@[stacks 0B4N] #check
  (@RationalSingularity.ReductionPossible : (A : Type u) → [CommRing A] → Prop)
