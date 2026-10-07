module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Retracts of perfect derived objects

Perfect objects in a derived category of modules are closed under retracts. This leaf owns the
reusable instance and its binary-biproduct consequence.

@stack 066S
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ObjectProperty

universe u

namespace DerivedCategory

variable {R : Type u} [Ring R]

/-- Lemma 15.75.5: perfect objects of `DerivedCategory (ModuleCat R)` are stable under
retracts. -/
@[stacks 066S "perfect derived objects are stable under retracts"]
instance isPerfect_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (IsPerfect : ObjectProperty (DerivedCategory (ModuleCat R))) := sorry

/-- Lemma 15.75.5: both summands of a perfect binary biproduct are perfect. -/
@[stacks 066S "perfect binary biproduct summands"]
theorem isPerfect_summands_of_biprod
    (K L : DerivedCategory (ModuleCat R)) (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect ∧ L.IsPerfect := sorry

end DerivedCategory
