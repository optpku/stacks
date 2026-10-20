/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Diagonal
import StacksCheckRecall

/-!
# Diagonal of a quotient stack

The diagonal of the quotient stack `[U/R]` associated to a groupoid in
algebraic spaces is representable by algebraic spaces. Smoothness of the
groupoid is not required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 94.17.1: let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`. Then the
diagonal of `[U/R]` is representable by algebraic spaces. Formalized for a
groupoid `G` in algebraic spaces over an algebraic space `B` over `S`, with
`[U/R]` as `GroupoidAlgebraicSpace.SmallQuotient.quotientStack G` and its
canonical diagonal. -/
@[stacks 04WZ] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.relativelyRepresentableByAlgebraicSpaces_diagonal :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
          (GroupoidAlgebraicSpace.SmallQuotient.quotientStack G)))

-- The isomorphism presheaves give the criterion for representability of the diagonal.
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isomorphismPresheaf_isAlgebraicSpace :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      isomorphismPresheaf.isAlgebraicSpace
        (GroupoidAlgebraicSpace.SmallQuotient.quotientStack G))
