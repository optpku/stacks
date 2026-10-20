/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer

/-!
# Split equalizers in opposite categories

An explicit split equalizer determines an explicit split coequalizer after passing to the
opposite category.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.IsSplitEqualizer

variable {C : Type u} [Category.{v} C]
variable {X Y W : C} {f g : X ⟶ Y} {ι : W ⟶ X}

/-- The equalizing condition becomes the coequalizing condition after taking opposites. -/
theorem op_condition (q : IsSplitEqualizer f g ι) :
    f.op ≫ ι.op = g.op ≫ ι.op := sorry

/-- The opposite of the left retraction is a right section. -/
theorem op_rightSection_π (q : IsSplitEqualizer f g ι) :
    q.leftRetraction.op ≫ ι.op = 𝟙 (Opposite.op W) := sorry

/-- The opposite of the right retraction splits the lower arrow. -/
theorem op_leftSection_bottom (q : IsSplitEqualizer f g ι) :
    q.rightRetraction.op ≫ g.op = 𝟙 (Opposite.op X) := sorry

/-- The remaining split-equalizer identity becomes the corresponding split-coequalizer identity. -/
theorem op_leftSection_top (q : IsSplitEqualizer f g ι) :
    q.rightRetraction.op ≫ f.op = ι.op ≫ q.leftRetraction.op := sorry

/-- An explicit split equalizer gives an explicit split coequalizer in the opposite category. -/
def op (q : IsSplitEqualizer f g ι) :
    IsSplitCoequalizer f.op g.op ι.op where
  rightSection := q.leftRetraction.op
  leftSection := q.rightRetraction.op
  condition := q.op_condition
  rightSection_π := q.op_rightSection_π
  leftSection_bottom := q.op_leftSection_bottom
  leftSection_top := q.op_leftSection_top

end CategoryTheory.IsSplitEqualizer
