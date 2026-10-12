/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory GradedModule

universe x w v u

variable {ι : Type x}
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable [DecidableEq ι] [AddCommMonoid ι]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/- Example 22.25.6 (Graded category of graded modules) (09MN): right graded modules over a
mathlib `GradedAlgebra` form a graded linear category whose total morphisms are finite sums of
homogeneous right-linear maps. -/
@[stacks 09MN] #check
  (Right.gradedCategory (𝒜 := 𝒜) :
    GradedCategory R (Right (R := R) (A := A) 𝒜) ι)

/- Homogeneous composition adds degrees and is exposed independently of totalization. -/
#check @Right.HomogeneousMap.comp

/- Total morphisms have a canonical map to their underlying right-linear maps. -/
#check @Right.Hom.toLinearMap

/- The degree-zero category has precisely the grading-preserving right-linear maps. -/
#check @Right.degreeZeroHomEquiv
