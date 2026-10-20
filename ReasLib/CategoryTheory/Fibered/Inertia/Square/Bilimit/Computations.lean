/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Bilimit.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilimit cone computations for the relative-inertia square

This module exposes the definitional projection formulas for the canonical
relative-inertia pseudo-pullback cone.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory
namespace BasedCategory

open BasedNatIso BasedNatTrans
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X Y : BasedCategory.{max v vB, max w (max u (max v vB))} C}

namespace RelativeInertia

namespace Square

/-- The apex of the canonical relative-inertia square is based relative inertia. -/
@[simp, stacks 04Z6 "relative-inertia square bilimit apex computation"]
theorem cone.pt (F : X ⥤ᵇ Y) :
    (cone F).pt = relativeInertia F := sorry
/- Proof strategy: unfold `cone`. -/

/-- The first leg of the canonical relative-inertia square projects to the target. -/
@[simp, stacks 04Z6 "relative-inertia square bilimit first leg computation"]
theorem cone.fst (F : X ⥤ᵇ Y) :
    (cone F).fst = toTarget F := sorry
/- Proof strategy: unfold `cone`. -/

/-- The second leg of the canonical relative-inertia square forgets the relative condition. -/
@[simp, stacks 04Z6 "relative-inertia square bilimit second leg computation"]
theorem cone.snd (F : X ⥤ᵇ Y) :
    (cone F).snd = RelativeInertia.toInertia F := sorry
/- Proof strategy: unfold `cone`. -/

/-- The comparison cell of the canonical relative-inertia square is `comparisonIso F`. -/
@[simp, stacks 04Z6 "relative-inertia square bilimit comparison computation"]
theorem cone.iso (F : X ⥤ᵇ Y) :
    (cone F).iso = comparisonIso F := sorry
/- Proof strategy: unfold `cone`. -/

end Square

end RelativeInertia

end BasedCategory
end CategoryTheory
