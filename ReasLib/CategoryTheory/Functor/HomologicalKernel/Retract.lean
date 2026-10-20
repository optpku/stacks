module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Retracts in Homological Kernels

The homological kernel of a functor is defined by objectwise vanishing after every shift.
This condition is stable under retracts independently of any homologicality assumption on the
functor.  The direct-summand formulation is exposed as a companion theorem.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits ObjectProperty

variable {C : Type u₁} {A : Type u₂}
  [Category.{v₁} C] [Category.{v₂} A] [HasShift C ℤ]
  (F : C ⥤ A)

/-- Stacks 05RD: the homological kernel of a functor is stable under retracts.  This only uses
the vanishing condition defining `F.homologicalKernel`; it does not require `F` to be
homological. -/
@[stacks 05RD "retract stability of homological kernels"]
instance homologicalKernel_isStableUnderRetracts :
    F.homologicalKernel.IsStableUnderRetracts := sorry

/-- Stacks 05RD: if a binary biproduct belongs to a homological kernel, then each summand does. -/
@[stacks 05RD "direct summands of homological kernels"]
theorem homologicalKernel_of_biprod
    [HasZeroMorphisms C] {X Y : C} [HasBinaryBiproduct X Y]
    (hXY : F.homologicalKernel (X ⊞ Y)) :
    F.homologicalKernel X ∧ F.homologicalKernel Y := sorry


end CategoryTheory.Functor
