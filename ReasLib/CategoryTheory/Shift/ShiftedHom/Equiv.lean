/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Moving a shift between source and target

The inverse-shift adjunction identifies maps into a shifted target with maps out of the
oppositely shifted source.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.ShiftedHom

variable {M : Type*} [AddGroup M]
variable {C : Type u} [Category.{v} C] [HasShift C M]

/-- A shifted morphism `X ⟶ Y⟦n⟧` is canonically a morphism `X⟦-n⟧ ⟶ Y`. -/
@[stacks 09MG]
noncomputable def sourceShiftEquiv (X Y : C) (n : M) :
    ShiftedHom X Y n ≃ (X⟦-n⟧ ⟶ Y) :=
  ((shiftEquiv C n).symm.toAdjunction.homEquiv X Y).symm

end CategoryTheory.ShiftedHom
