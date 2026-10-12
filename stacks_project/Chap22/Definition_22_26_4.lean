/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.DirectSum
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [DifferentialGradedCategory.{u, v, w} R C]
variable (x y : DifferentialGradedCategory.Comp R C)

/- Definition 22.26.4 (09P4): a differential graded direct sum is canonical biproduct data in
the category whose arrows are closed homogeneous maps of degree zero.  Thus all four structure
maps have exactly the degree and closedness required in the source definition. -/
@[stacks 09P4] #check
  (Limits.BinaryBiproductData x y : Type _)

#check @DifferentialGradedCategory.binaryBiproductDataOfTotal
