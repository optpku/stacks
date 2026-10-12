/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Lemma_94_10_11

/-!
# Fibre products and equalizers of groupoid fibrations

A category fibred in groupoids over `(Sch/S)_fppf` has fibre products. If its
Isom-presheaves are algebraic spaces, it has equalizers. Algebraic stacks, and
more generally quotient stacks, have equalizers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Lemma 96.17.2 (1): a category `X` fibred in groupoids over `(Sch/S)_fppf`
has fibre products, i.e. `X.total` has limits of shape `WalkingCospan`. -/
@[stacks 06WY]
instance hasPullbacks (X : GroupoidsOver S) : HasPullbacks X.total := sorry

/-- Lemma 96.17.2 (2): if the Isom-presheaves of a category `X` fibred in
groupoids over `(Sch/S)_fppf` are representable by algebraic spaces, then
`X.total` has equalizers. -/
@[stacks 06WY]
theorem hasEqualizers_of_isomorphismPresheaf (X : GroupoidsOver S)
    (h : isomorphismPresheaf.isAlgebraicSpace X) :
    HasEqualizers X.total := sorry

/-- Lemma 96.17.2 (3): the quotient stack `[U/R]` associated to a groupoid in
algebraic spaces has equalizers. -/
@[stacks 06WY]
instance hasEqualizers_quotientStack {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    HasEqualizers G.quotientStack.total := sorry

/-- Lemma 96.17.2 (3): an algebraic stack over `S` has equalizers. -/
@[stacks 06WY]
instance hasEqualizers (X : GroupoidsOver S) [AlgebraicStack X] :
    HasEqualizers X.total := sorry

end AlgebraicGeometry.GroupoidsOver
