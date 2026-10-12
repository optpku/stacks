/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Graded
import StacksCheckRecall

universe x w v u

open CategoryTheory

variable (R : Type w) [Semiring R]
variable (C : Type u) [Category.{v} C] [Preadditive C]
variable (ι : Type x) [DecidableEq ι] [AddMonoid ι]

/- Definition 22.25.1 [09L2]: an `R`-linear category with a homogeneous direct-sum
decomposition of every hom module, indexed by an additive monoid `ι`, is canonically represented
by `GradedCategory`; the source's integer grading is the specialization `ι = ℤ`. -/
@[stacks 09L2] #check (GradedCategory R C ι : Type _)
