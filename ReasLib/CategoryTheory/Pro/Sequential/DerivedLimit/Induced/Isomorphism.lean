/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.DerivedLimit.Induced.First
public import ReasLib.CategoryTheory.Pro.Sequential.DerivedLimit.Induced.Limit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pro-isomorphism invariance of sequential derived limits

This file combines the independent invariance statements for inverse limits and their neutral
canonical Milnor-cokernel models into the source-facing Stacks Project result.
@stack 0H9K
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SequentialInverseSystem C}
variable [HasLimitsOfShape ℕᵒᵖ C] [HasCountableProducts C] [HasCokernels C]

namespace Quotient

/-- Lemma 15.87.4 (Stacks 0H9K): a sequential morphism class representing a pro-isomorphism
induces isomorphisms on both the inverse limit and its neutral canonical Milnor cokernel. -/
@[stacks 0H9K]
theorem maps_isIso
    (η : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    [IsIso (quotientToHom η)] :
    IsIso (limitMap η) ∧ IsIso (firstDerivedLimitMap η) := sorry

end Quotient

end CategoryTheory.Pro.SequentialHom
