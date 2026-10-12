/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Opposites of arrow categories

Mathlib constructs opposites for arbitrary comma categories.  This file specializes that
construction to arrows, exposing the variance and the exchanged source and target directly at
the `Arrow` layer.  In particular, a square `f ⟶ g` induces a square from the opposite of `g` to
the opposite of `f`.
-/

@[expose] public section

open Opposite

universe v u

namespace CategoryTheory.Arrow

variable (C : Type u) [Category.{v} C]

/-- The contravariant operation which reverses every arrow and every commutative square. -/
@[stacks 019Z "opposite-arrow functor"]
def opFunctor : (Arrow C)ᵒᵖ ⥤ Arrow Cᵒᵖ :=
  (Comma.opFunctor (𝟭 C) (𝟭 C)).leftOp

namespace opFunctor

/-- Reversing an arrow exchanges its source with the opposite of its target. -/
@[simp] theorem obj_left (f : (Arrow C)ᵒᵖ) :
    ((opFunctor C).obj f).left = op f.unop.right := sorry

/-- Reversing an arrow exchanges its target with the opposite of its source. -/
@[simp] theorem obj_right (f : (Arrow C)ᵒᵖ) :
    ((opFunctor C).obj f).right = op f.unop.left := sorry

/-- The underlying morphism of the reversed arrow is the opposite morphism. -/
@[simp] theorem obj_hom (f : (Arrow C)ᵒᵖ) :
    ((opFunctor C).obj f).hom = f.unop.hom.op := sorry

/-- On an explicitly presented arrow, `opFunctor` is the arrow built from the opposite map. -/
@[simp] theorem obj_mk {X Y : C} (f : X ⟶ Y) :
    (opFunctor C).obj (op (Arrow.mk f)) = Arrow.mk f.op := sorry

/-- On squares, the left component is the opposite of the original right component. -/
@[simp] theorem map_left {f g : (Arrow C)ᵒᵖ} (α : f ⟶ g) :
    ((opFunctor C).map α).left = α.unop.right.op := sorry

/-- On squares, the right component is the opposite of the original left component. -/
@[simp] theorem map_right {f g : (Arrow C)ᵒᵖ} (α : f ⟶ g) :
    ((opFunctor C).map α).right = α.unop.left.op := sorry

end opFunctor

/-- The inverse operation, reversing an arrow and a square in the opposite category back into
the original category. -/
@[stacks 019Z "inverse opposite-arrow functor"]
def unopFunctor : Arrow Cᵒᵖ ⥤ (Arrow C)ᵒᵖ :=
  Comma.unopFunctor (𝟭 C) (𝟭 C)

namespace unopFunctor

/-- Unopposing a reversed arrow recovers the original target as its source. -/
@[simp] theorem obj_left (f : Arrow Cᵒᵖ) :
    ((unopFunctor C).obj f).unop.left = f.right.unop := sorry

/-- Unopposing a reversed arrow recovers the original source as its target. -/
@[simp] theorem obj_right (f : Arrow Cᵒᵖ) :
    ((unopFunctor C).obj f).unop.right = f.left.unop := sorry

/-- The underlying map of an unopposed arrow is the unopposite morphism. -/
@[simp] theorem obj_hom (f : Arrow Cᵒᵖ) :
    ((unopFunctor C).obj f).unop.hom = f.hom.unop := sorry

/-- On an explicitly presented opposite arrow, `unopFunctor` is the arrow built from the
unopposite map. -/
@[simp] theorem obj_mk {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((unopFunctor C).obj (Arrow.mk f)).unop = Arrow.mk f.unop := sorry

/-- On squares, unopposing exchanges the right component with the underlying left component. -/
@[simp] theorem map_left {f g : Arrow Cᵒᵖ} (α : f ⟶ g) :
    ((unopFunctor C).map α).unop.left = α.right.unop := sorry

/-- On squares, unopposing exchanges the left component with the underlying right component. -/
@[simp] theorem map_right {f g : Arrow Cᵒᵖ} (α : f ⟶ g) :
    ((unopFunctor C).map α).unop.right = α.left.unop := sorry

end unopFunctor

/-- Reversing arrows identifies the opposite of `Arrow C` with `Arrow Cᵒᵖ`. -/
@[stacks 019Z "opposite-arrow category equivalence"]
def opEquivalence : (Arrow C)ᵒᵖ ≌ Arrow Cᵒᵖ :=
  (Comma.opEquiv (𝟭 C) (𝟭 C)).leftOp

namespace opEquivalence

/-- The forward functor of the opposite-arrow equivalence is `Arrow.opFunctor`. -/
@[simp] theorem functor_eq : (opEquivalence C).functor = opFunctor C := sorry

/-- The inverse functor of the opposite-arrow equivalence is `Arrow.unopFunctor`. -/
@[simp] theorem inverse_eq : (opEquivalence C).inverse = unopFunctor C := sorry

end opEquivalence

namespace opFunctor

/-- Reversing commutative squares is an equivalence of arrow categories. -/
instance isEquivalence : (opFunctor C).IsEquivalence := sorry

end opFunctor

namespace unopFunctor

/-- Unopposing commutative squares is an equivalence of arrow categories. -/
instance isEquivalence : (unopFunctor C).IsEquivalence := sorry

end unopFunctor

end CategoryTheory.Arrow
