module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of Externally Graded Modules

Limits and colimits of externally graded right modules are computed degreewise.  Shape-wise
instances are universe-safe: they are available whenever the corresponding limits or colimits
exist in the category of modules over the base ring.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.Graded

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (J : Type x) [Category.{y} J]

/-- Lemma 22.4.2 (09JJ): externally graded right `A`-modules have limits of every shape
available in `ModuleCat R`. -/
@[stacks 09JJ "limits of externally graded modules"]
instance hasLimitsOfShape [HasLimitsOfShape J (ModuleCat.{w} R)] :
    HasLimitsOfShape J (Graded.{u, v, w} A) := sorry

/-- Lemma 22.4.2 (09JJ): externally graded right `A`-modules have colimits of every shape
available in `ModuleCat R`. -/
@[stacks 09JJ "colimits of externally graded modules"]
instance hasColimitsOfShape [HasColimitsOfShape J (ModuleCat.{w} R)] :
    HasColimitsOfShape J (Graded.{u, v, w} A) := sorry

/-- Evaluation in one degree preserves all limits that exist in the base module category. -/
instance evalPreservesLimitsOfShape [HasLimitsOfShape J (ModuleCat.{w} R)] (n : ℤ) :
    PreservesLimitsOfShape J (eval.{u, v, w} A n) := sorry

/-- Evaluation in one degree preserves all colimits that exist in the base module category. -/
instance evalPreservesColimitsOfShape [HasColimitsOfShape J (ModuleCat.{w} R)] (n : ℤ) :
    PreservesColimitsOfShape J (eval.{u, v, w} A n) := sorry

/-- Forgetting the graded `A`-action preserves limits. -/
instance forgetActionPreservesLimitsOfShape [HasLimitsOfShape J (ModuleCat.{w} R)] :
    PreservesLimitsOfShape J (forgetAction.{u, v, w} A) := sorry

/-- Forgetting the graded `A`-action preserves colimits. -/
instance forgetActionPreservesColimitsOfShape [HasColimitsOfShape J (ModuleCat.{w} R)] :
    PreservesColimitsOfShape J (forgetAction.{u, v, w} A) := sorry

end DifferentialGradedModule.Graded
