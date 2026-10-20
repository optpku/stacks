/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X : C)

/- Lemma 4.43.3: left tensoring, right tensoring, and existence of a two-sided tensor inverse are
equivalent for a fixed object of a monoidal category. -/
@[stacks 0FFM]
#check (MonoidalCategory.isInvertibleObject.tfae X :
  List.TFAE [
    (tensorLeft X).IsEquivalence,
    (tensorRight X).IsEquivalence,
    ∃ X' : C,
      Nonempty (X ⊗ X' ≅ 𝟙_ C) ∧ Nonempty (X' ⊗ X ≅ 𝟙_ C)
  ])

end CategoryTheory
