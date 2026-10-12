/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.Setoids.PseudoPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Thin fibers of two-fibre products of stacks

This file specializes the neutral mixed setoid-closure API for based pseudo-pullbacks to the
canonical two-fibre product of stacks. The apex and its universal property remain owned by
`TwoFibreProduct.Basic`; stack descent is the only property added at this layer.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids

namespace TwoFibreProduct

variable {X Y Z : StackOver.Groupoids J}

/-- Every fiber of the canonical two-fibre product is thin when the left cospan leg is faithful
and the right source has thin fibers. This is the fiberwise view of
`BasedCategory.PseudoPullback.Projection.InSetoids.ofCartesianLeft`. -/
@[stacks 05UI "fiberwise thinness of the left-faithful two-fibre product"]
theorem fiber_isThin_of_left
    (F : X ⟶ Z) (G : Y ⟶ Z)
    [(Hom.toBasedFunctor F).Faithful] [Functor.IsFibered.InSetoids Y.p]
    (U : C) :
    Quiver.IsThin ((apex F G).p.Fiber U) := sorry

/-- Explicit-proof form of `fiber_isThin_of_left`, for consumers that keep faithfulness as a
term instead of installing it as a local instance. -/
@[stacks 05UI "explicit left-faithfulness fiber thinness bridge"]
theorem fiber_isThin_of_left_of_faithful
    (F : X ⟶ Z) (G : Y ⟶ Z)
    (hF : (Hom.toBasedFunctor F).Faithful)
    [Functor.IsFibered.InSetoids Y.p] (U : C) :
    Quiver.IsThin ((apex F G).p.Fiber U) := sorry

/-- The canonical two-fibre product has setoid fibers when the left cospan leg is faithful and
the right source has setoid fibers. The neutral mixed closure theorem is
`BasedCategory.PseudoPullback.Projection.InSetoids.ofCartesianLeft`. -/
@[stacks 05UI "setoid-fiber closure of the left-faithful two-fibre product"]
theorem isFiberedInSetoids_of_left
    (F : X ⟶ Z) (G : Y ⟶ Z)
    [(Hom.toBasedFunctor F).Faithful] [Functor.IsFibered.InSetoids Y.p] :
    Functor.IsFibered.InSetoids (apex F G).p := sorry

/-- Explicit-proof form of `isFiberedInSetoids_of_left`. -/
@[stacks 05UI "explicit left-faithfulness setoid-fiber bridge"]
theorem isFiberedInSetoids_of_left_of_faithful
    (F : X ⟶ Z) (G : Y ⟶ Z)
    (hF : (Hom.toBasedFunctor F).Faithful)
    [Functor.IsFibered.InSetoids Y.p] :
    Functor.IsFibered.InSetoids (apex F G).p := sorry

/-- A two-fibre product of stacks in groupoids is a stack in setoids when the left leg is
faithful and the right source has setoid fibers. -/
@[stacks 05UI]
theorem isStackInSetoids_of_left
    (F : X ⟶ Z) (G : Y ⟶ Z)
    [(Hom.toBasedFunctor F).Faithful] [Functor.IsFibered.InSetoids Y.p] :
    IsStack.InSetoids J (apex F G).p := sorry

/-- Explicit-proof form of `isStackInSetoids_of_left`. -/
@[stacks 05UI "explicit left-faithfulness stack-in-setoids bridge"]
theorem isStackInSetoids_of_left_of_faithful
    (F : X ⟶ Z) (G : Y ⟶ Z)
    (hF : (Hom.toBasedFunctor F).Faithful)
    [Functor.IsFibered.InSetoids Y.p] :
    IsStack.InSetoids J (apex F G).p := sorry

/-- Every fiber of the canonical two-fibre product is thin when the right cospan leg is faithful
and the left source has thin fibers. This is the fiberwise view of
`BasedCategory.PseudoPullback.Projection.InSetoids.ofCartesianRight`. -/
@[stacks 05UI "fiberwise thinness of the right-faithful two-fibre product"]
theorem fiber_isThin_of_right
    (F : X ⟶ Z) (G : Y ⟶ Z)
    [(Hom.toBasedFunctor G).Faithful] [Functor.IsFibered.InSetoids X.p]
    (U : C) :
    Quiver.IsThin ((apex F G).p.Fiber U) := sorry

/-- Explicit-proof form of `fiber_isThin_of_right`, for consumers that keep faithfulness as a
term instead of installing it as a local instance. -/
@[stacks 05UI "explicit right-faithfulness fiber thinness bridge"]
theorem fiber_isThin_of_right_of_faithful
    (F : X ⟶ Z) (G : Y ⟶ Z)
    (hG : (Hom.toBasedFunctor G).Faithful)
    [Functor.IsFibered.InSetoids X.p] (U : C) :
    Quiver.IsThin ((apex F G).p.Fiber U) := sorry

/-- The canonical two-fibre product has setoid fibers when the right cospan leg is faithful and
the left source has setoid fibers. The neutral mixed closure theorem is
`BasedCategory.PseudoPullback.Projection.InSetoids.ofCartesianRight`. -/
@[stacks 05UI "setoid-fiber closure of the right-faithful two-fibre product"]
theorem isFiberedInSetoids_of_right
    (F : X ⟶ Z) (G : Y ⟶ Z)
    [(Hom.toBasedFunctor G).Faithful] [Functor.IsFibered.InSetoids X.p] :
    Functor.IsFibered.InSetoids (apex F G).p := sorry

/-- Explicit-proof form of `isFiberedInSetoids_of_right`. -/
@[stacks 05UI "explicit right-faithfulness setoid-fiber bridge"]
theorem isFiberedInSetoids_of_right_of_faithful
    (F : X ⟶ Z) (G : Y ⟶ Z)
    (hG : (Hom.toBasedFunctor G).Faithful)
    [Functor.IsFibered.InSetoids X.p] :
    Functor.IsFibered.InSetoids (apex F G).p := sorry

/-- A two-fibre product of stacks in groupoids is a stack in setoids when the right leg is
faithful and the left source has setoid fibers. -/
@[stacks 05UI "right-leg setoid closure"]
theorem isStackInSetoids_of_right
    (F : X ⟶ Z) (G : Y ⟶ Z)
    [(Hom.toBasedFunctor G).Faithful] [Functor.IsFibered.InSetoids X.p] :
    IsStack.InSetoids J (apex F G).p := sorry

/-- Explicit-proof form of `isStackInSetoids_of_right`. -/
@[stacks 05UI "explicit right-faithfulness stack-in-setoids bridge"]
theorem isStackInSetoids_of_right_of_faithful
    (F : X ⟶ Z) (G : Y ⟶ Z)
    (hG : (Hom.toBasedFunctor G).Faithful)
    [Functor.IsFibered.InSetoids X.p] :
    IsStack.InSetoids J (apex F G).p := sorry

end TwoFibreProduct

end StackOver.Groupoids

end CategoryTheory
