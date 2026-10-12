/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left exactness in degree zero

The degree-zero branch of a cohomological delta functor is left exact. This is a property of the
abstract delta-functor interface, not of any particular complex or geometric construction.
-/

@[expose] public section

open CategoryTheory.Limits

universe vA vB uA uB

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The degree-zero branch of a cohomological delta functor preserves finite limits. -/
@[stacks 010Q "degree-zero left exactness of a cohomological delta functor"]
instance degreeZeroPreservesFiniteLimits (F : CohomologicalDeltaFunctor A B) :
    PreservesFiniteLimits (F.F 0).obj := sorry

end CategoryTheory.CohomologicalDeltaFunctor
