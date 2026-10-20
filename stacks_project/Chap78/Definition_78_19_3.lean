module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Representable
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory AlgebraicSpace

/- Definition 78.19.3 (1): a pre-relation has a quotient representable by an algebraic space
when the sheaf `U/R` is an algebraic space. -/
@[stacks 044L] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.HasAlgebraicSpaceQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
      PreRelation U → Prop)

/- Definition 78.19.3 (2): a pre-relation has a representable quotient when the sheaf `U/R`
is representable by a scheme. -/
@[stacks 044L] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.HasRepresentableQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
      PreRelation U → Prop)

/- Definition 78.19.3 (3): a groupoid in algebraic spaces has a representable quotient when
the quotient of `j = (t, s)` is representable. -/
@[stacks 044L] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.HasRepresentableQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
      GroupoidAlgebraicSpace B → Prop)

/- Definition 78.19.3 (4): a groupoid in algebraic spaces has a quotient representable by an
algebraic space when the quotient of `j = (t, s)` is an algebraic space. -/
@[stacks 044L] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.HasAlgebraicSpaceQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
      GroupoidAlgebraicSpace B → Prop)
