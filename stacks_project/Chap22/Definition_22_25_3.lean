/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Graded.DegreeZero
import StacksCheckRecall

universe x w v u

open CategoryTheory

variable {R : Type w} [Semiring R]
variable (C : Type u) [Category.{v} C] [Preadditive C]
variable (ι : Type x) [DecidableEq ι] [AddMonoid ι]
variable [GradedCategory R C ι]

/- Definition 22.25.3 [09ML]: the category with the same objects and only degree-zero
morphisms is canonically represented by `GradedCategory.DegreeZero`. -/
@[stacks 09ML] #check
  (GradedCategory.DegreeZero C ι : Type u)
