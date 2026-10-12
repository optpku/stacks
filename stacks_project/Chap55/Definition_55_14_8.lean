/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap55.Definition_55_14_8_GoodReduction

/- Definition 55.14.8: Let `R` be a discrete valuation ring with fraction field `K`,
and let `C` be a smooth projective curve over `K` such that
`Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)`. The curve `C` has good
reduction when the equivalent conditions of Lemma 55.14.7 hold. -/
@[stacks 0CDJ] #check AlgebraicGeometry.Scheme.Hom.hasGoodReduction
