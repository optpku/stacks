/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Limits of Retracts of Diagrams

In an idempotent-complete target category, the property that a diagram admits a colimit or a
limit is stable under retracts in the functor category.  These instances put that fact at the
generic object-property layer, so direct-summand applications can use Mathlib's existing retract
API without rebuilding split idempotents locally.
-/

@[expose] public section

open CategoryTheory.ObjectProperty

universe uJ vJ uC vC

namespace CategoryTheory.Limits

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- In an idempotent-complete category, admitting a colimit is stable under retracts of
diagrams. -/
instance hasColimit_isStableUnderRetracts [IsIdempotentComplete C] :
    IsStableUnderRetracts (fun F : J ⥤ C ↦ HasColimit F) := sorry

/-- In an idempotent-complete category, admitting a limit is stable under retracts of
diagrams. -/
instance hasLimit_isStableUnderRetracts [IsIdempotentComplete C] :
    IsStableUnderRetracts (fun F : J ⥤ C ↦ HasLimit F) := sorry

end CategoryTheory.Limits
