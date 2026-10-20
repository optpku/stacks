/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.CommSq.Lift
import StacksCheckRecall
import stacks_project.Chap32.«32_15_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

section

variable {X S : Scheme.{u}} {f : X ⟶ S} (sq : ValuativeCommSq f)

/- 32.15.2.3: once the solid valuative diagram from `32.15.2.1` is viewed as its underlying
commutative square, the source claim that no dotted arrow `Spec(A) ⟶ X` exists is exactly the
statement that the canonical type of dotted-arrow lifts is empty. -/
@[stacks 05M2] #check
  (CategoryTheory.CommSq.not_hasLift_iff_isEmpty sq.commSq :
    ¬ sq.commSq.HasLift ↔ IsEmpty sq.commSq.LiftStruct)

end
