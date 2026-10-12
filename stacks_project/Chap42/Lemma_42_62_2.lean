/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_62_2_Comparison
import StacksCheckRecall

/- Lemma 42.62.2 (1): for a field `k` and a scheme `X` smooth over `k` and
equidimensional of dimension `d`, the map `A^p(X) ⟶ CH_{d-p}(X)` given by
`c ↦ c ∩ [X]_d` is an isomorphism. -/
@[stacks 0FC2] #check @AlgebraicGeometry.BivariantClass.capFundamentalEquiv

/- Lemma 42.62.2 (2): via this isomorphism, composition of bivariant classes turns
into the intersection product. -/
@[stacks 0FC2] #check @AlgebraicGeometry.BivariantClass.capFundamental_comp
