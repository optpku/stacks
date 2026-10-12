/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_22_2_Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasSquare
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
