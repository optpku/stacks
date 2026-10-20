/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Right Kan extensions and the underlying-set functor on rings

The forgetful functor from rings preserves all limits, hence it preserves every pointwise right
Kan extension.  The named instance below exposes this consequence at the functor-family level
used by sheaf direct-image comparisons.
-/

@[expose] public section

open CategoryTheory

universe u₁ u₂ v₁ v₂ w

namespace RingCat

/-- The underlying-set functor on rings preserves limits whose object and morphism universes
may differ, provided that the object universe is bounded by the ring universe. -/
@[stacks 04IY "ring forgetful limits"]
instance (priority := high) forgetPreservesLimitsOfSize [UnivLE.{u₁, w}] :
    Limits.PreservesLimitsOfSize.{v₁, u₁} (forget RingCat.{w}) := sorry

end RingCat

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable [UnivLE.{max u₁ v₂, w}]

/-- The underlying-set functor on rings preserves every pointwise right Kan extension. -/
instance forgetRing_preservesPointwiseRightKanExtension
    (F : A ⥤ RingCat.{w}) (L : A ⥤ B) :
    (forget RingCat.{w}).PreservesPointwiseRightKanExtension F L := sorry

/-- The underlying-set functor on rings preserves right Kan extensions whenever the chosen
extensions are pointwise. -/
@[stacks 04IY "ring forgetful right Kan"]
instance forgetRing_preservesRightKanExtensions (L : A ⥤ B)
    [∀ F : A ⥤ RingCat.{w}, L.HasPointwiseRightKanExtension F] :
    (forget RingCat.{w}).PreservesRightKanExtensions L := sorry

-- This instance is obtained solely from the canonical limit-preservation instance for
-- `forget RingCat` and the supplied pointwise right Kan extensions.

end CategoryTheory.Functor
