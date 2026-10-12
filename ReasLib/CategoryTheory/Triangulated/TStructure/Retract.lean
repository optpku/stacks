/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Retract closure of t-structure bounds

The two halves of a t-structure, and hence its bounded-above, bounded-below, and bounded
object properties, are closed under retracts.  Named instances make this closure available to
generic full-subcategory and idempotent-splitting APIs.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Triangulated.TStructure

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace le

/-- The nonpositive half of a t-structure in any degree is closed under retracts. -/
instance isStableUnderRetracts (t : TStructure C) (n : ℤ) :
    (t.le n).IsStableUnderRetracts := sorry

end le

namespace ge

/-- The nonnegative half of a t-structure in any degree is closed under retracts. -/
instance isStableUnderRetracts (t : TStructure C) (n : ℤ) :
    (t.ge n).IsStableUnderRetracts := sorry

end ge

namespace minus

/-- The bounded-above objects of a t-structure are closed under retracts. -/
@[stacks 05RU "bounded-above t-structure objects are retract-closed"]
instance isStableUnderRetracts (t : TStructure C) :
    t.minus.IsStableUnderRetracts := sorry

end minus

namespace plus

/-- The bounded-below objects of a t-structure are closed under retracts. -/
@[stacks 05RU "bounded-below t-structure objects are retract-closed"]
instance isStableUnderRetracts (t : TStructure C) :
    t.plus.IsStableUnderRetracts := sorry

end plus

namespace bounded

/-- The bounded objects of a t-structure are closed under retracts. -/
instance isStableUnderRetracts (t : TStructure C) :
    t.bounded.IsStableUnderRetracts := sorry

end bounded


variable (t : TStructure C) (n : ℤ)

#synth (t.le n).IsStableUnderRetracts
#synth (t.ge n).IsStableUnderRetracts
#synth t.minus.IsStableUnderRetracts
#synth t.plus.IsStableUnderRetracts
#synth t.bounded.IsStableUnderRetracts

end CategoryTheory.Triangulated.TStructure
