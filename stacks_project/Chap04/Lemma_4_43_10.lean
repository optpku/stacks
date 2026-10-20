/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X Y : C} [ExactPairing X Y]

/- `ExactPairing X Y`, recalled in Definition 4.43.5, is the fixed-pair owner needed by the
source. The installed alternatives `hasLeftDualOfHasRightDual` and
`hasRightDualOfHasLeftDual` choose a dual object, whereas
`BraidedCategory.exactPairing_swap` preserves the specified `X` and `Y` and constructs the
swapped pairing with coevaluation `η_ X Y ≫ (β_ Y X).inv` and evaluation
`(β_ X Y).hom ≫ ε_ X Y`. Checking this construction in the source symmetric context,
rather than recalling its more general braided type, recovers the exact source hypotheses and
leaves downstream users with mathlib canonical pairing API instead of a local alias. -/

/- Lemma 4.43.10: if `Y` is a left dual of `X` in a symmetric monoidal category, swapping the
coevaluation and evaluation through the symmetry makes `X` a left dual of `Y`. -/
@[stacks 0FN8 "swapping a specified left dual through the symmetry"]
#check (BraidedCategory.exactPairing_swap X Y : ExactPairing Y X)

end CategoryTheory
