/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for groupoid-fibred diagonals

This leaf exposes the two projection isomorphisms of the canonical diagonal as components of the
universal comparison modification.  It contains no new diagonal data.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Bicategory
open scoped Pseudofunctor.StrongTrans

universe u v w

namespace CategoryTheory

namespace FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

namespace Hom.diagonal

/-- The forward first-projection comparison is the left-vertex component of the universal
comparison modification. -/
@[simp]
theorem fstIso.hom (F : X ⟶ Y) :
    (fstIso F).hom =
      (comparisonIso F).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry

/-- The inverse first-projection comparison is the left-vertex component of the inverse
universal comparison modification. -/
@[simp]
theorem fstIso.inv (F : X ⟶ Y) :
    (fstIso F).inv =
      (comparisonIso F).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry

/-- The forward second-projection comparison is the right-vertex component of the universal
comparison modification. -/
@[simp]
theorem sndIso.hom (F : X ⟶ Y) :
    (sndIso F).hom =
      (comparisonIso F).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry

/-- The inverse second-projection comparison is the right-vertex component of the inverse
universal comparison modification. -/
@[simp]
theorem sndIso.inv (F : X ⟶ Y) :
    (sndIso F).inv =
      (comparisonIso F).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry

end Hom.diagonal

end FiberedCategoryOver.Groupoids

end CategoryTheory
