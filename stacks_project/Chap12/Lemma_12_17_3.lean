/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Duality.Retract
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsIdempotentComplete C]
variable {X Y : C} [HasLeftDual Y]

/- Lemma 12.17.3: a retract of a left-dualizable object is left dualizable.  The existence
statement keeps the noncanonical idempotent splitting out of typeclass inference. -/
@[stacks 0FFU] #check
  (Retract.existsHasLeftDual : Retract X Y → Nonempty (HasLeftDual X))

/- An explicit splitting of the mate projector gives concrete pairing and left-dual data. -/
#check Retract.LeftDualSplit.exactPairing
#check Retract.LeftDualSplit.hasLeftDual

end CategoryTheory
