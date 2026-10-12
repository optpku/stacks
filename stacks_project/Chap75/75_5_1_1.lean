/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.«75_5_1_1_Comparison»
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- 75.5.1.1: the canonical functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 08F1] #check
  (DerivedQCoh.comparison X : DerivedCategory (QCoh X) ⥤ DerivedQCoh X)
