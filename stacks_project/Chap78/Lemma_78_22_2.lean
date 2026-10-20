module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets.Functoriality
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace
open scoped Bicategory

/- Lemma 78.22.2: the concrete source-target square with apex the stack for R
is a 2-fibre product over the canonical quotient stack. -/
@[stacks 04M9] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTargetCone_isBilimit :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      (sourceTargetCone G).IsBilimit)
