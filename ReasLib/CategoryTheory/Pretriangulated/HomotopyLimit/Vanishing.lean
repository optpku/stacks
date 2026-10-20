/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of sequential homotopy limits

This leaf relates the intrinsic homotopy-limit predicate to the Milnor difference on any
explicit product cone.  Keeping the cone explicit avoids installing a selected countable-product
instance and makes the criterion reusable outside derived categories.

@stack 08TC
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open SequentialInverseSystem.Milnor

universe u v

namespace CategoryTheory.HomotopyLimit.IsOf

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks `08TC`: a sequential homotopy-limit object vanishes exactly when the Milnor
difference on any explicitly supplied product cone is an isomorphism. -/
@[stacks 08TC "vanishing criterion for a sequential homotopy limit"]
theorem isZero_iff_difference_isIso {K : SequentialInverseSystem D} {X : D}
    (hX : HomotopyLimit.IsOf K X)
    (P : LimitCone (Discrete.functor K.family)) :
    IsZero X ↔
      IsIso (ProductCone.difference K P) := sorry

end CategoryTheory.HomotopyLimit.IsOf
