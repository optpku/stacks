/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap78.Definition_78_19_3_Representable
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory AlgebraicSpace

/- Definition 78.19.3 (1): a pre-relation has a quotient representable by an algebraic space
when the sheaf `U/R` is an algebraic space. -/
@[stacks 044L] #check
  (@PreRelation.HasAlgebraicSpaceQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
      PreRelation U → Prop)

/- Definition 78.19.3 (2): a pre-relation has a representable quotient when the sheaf `U/R`
is representable by a scheme. -/
@[stacks 044L] #check
  (@PreRelation.HasRepresentableQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
      PreRelation U → Prop)

/- Definition 78.19.3 (3): a groupoid in algebraic spaces has a representable quotient when
the quotient of `j = (t, s)` is representable. -/
@[stacks 044L] #check
  (@GroupoidAlgebraicSpace.HasRepresentableQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
      GroupoidAlgebraicSpace B → Prop)

/- Definition 78.19.3 (4): a groupoid in algebraic spaces has a quotient representable by an
algebraic space when the quotient of `j = (t, s)` is an algebraic space. -/
@[stacks 044L] #check
  (@GroupoidAlgebraicSpace.HasAlgebraicSpaceQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
      GroupoidAlgebraicSpace B → Prop)
