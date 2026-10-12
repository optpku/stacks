/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of Differential Graded Modules

The category of right differential graded modules has the same universe-safe shapes of limits
and colimits as modules over the base ring.  Both standard forgetful functors preserve them.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (J : Type x) [Category.{y} J]

/-- Lemma 22.4.2 (09JJ) (2): right DG `A`-modules have limits of every shape available in
`ModuleCat R`. -/
@[stacks 09JJ "limits of differential graded modules"]
instance hasLimitsOfShape [HasLimitsOfShape J (ModuleCat.{w} R)] :
    HasLimitsOfShape J (DifferentialGradedModule.{u, w} A) := sorry

/-- Lemma 22.4.2 (09JJ) (3): right DG `A`-modules have colimits of every shape available in
`ModuleCat R`. -/
@[stacks 09JJ "colimits of differential graded modules"]
instance hasColimitsOfShape [HasColimitsOfShape J (ModuleCat.{w} R)] :
    HasColimitsOfShape J (DifferentialGradedModule.{u, w} A) := sorry

/-- Finite limits of right DG `A`-modules are available without exposing a diagram-shape
parameter to downstream typeclass search. -/
instance hasFiniteLimits : HasFiniteLimits (DifferentialGradedModule.{u, w} A) := sorry

/-- Finite colimits of right DG `A`-modules are available without exposing a diagram-shape
parameter to downstream typeclass search. -/
instance hasFiniteColimits : HasFiniteColimits (DifferentialGradedModule.{u, w} A) := sorry

/-- Kernels of right DG-module morphisms are computed degreewise. -/
instance hasKernels : HasKernels (DifferentialGradedModule.{u, w} A) := sorry

/-- Cokernels of right DG-module morphisms are computed degreewise. -/
instance hasCokernels : HasCokernels (DifferentialGradedModule.{u, w} A) := sorry

/-- Countable products of right DG-modules are available through a universe-stable named
instance, so sequential and Milnor constructions do not need local instance pins. -/
instance hasCountableProducts :
    HasCountableProducts (DifferentialGradedModule.{u, w} A) := sorry

/-- Countable coproducts of right DG-modules are available through a universe-stable named
instance. -/
instance hasCountableCoproducts :
    HasCountableCoproducts (DifferentialGradedModule.{u, w} A) := sorry

/-- Sequential colimits of right differential graded modules are exact. -/
@[stacks 0CRL "exact sequential colimits of DG modules"]
instance hasExactSequentialColimits :
    HasExactColimitsOfShape ℕ (DifferentialGradedModule.{u, w} A) := sorry

/-- Forgetting only the differential preserves all limits. -/
instance forgetToGradedPreservesLimitsOfShape [HasLimitsOfShape J (ModuleCat.{w} R)] :
    PreservesLimitsOfShape J (forgetToGraded.{u, v, w} A) := sorry

/-- Forgetting only the differential preserves all colimits. -/
instance forgetToGradedPreservesColimitsOfShape [HasColimitsOfShape J (ModuleCat.{w} R)] :
    PreservesColimitsOfShape J (forgetToGraded.{u, v, w} A) := sorry

/-- The underlying cochain-complex functor preserves all limits. -/
instance forgetToComplexPreservesLimitsOfShape [HasLimitsOfShape J (ModuleCat.{w} R)] :
    PreservesLimitsOfShape J (forgetToComplex.{u, w} A) := sorry

/-- The underlying cochain-complex functor preserves all colimits. -/
instance forgetToComplexPreservesColimitsOfShape [HasColimitsOfShape J (ModuleCat.{w} R)] :
    PreservesColimitsOfShape J (forgetToComplex.{u, w} A) := sorry

end DifferentialGradedModule
