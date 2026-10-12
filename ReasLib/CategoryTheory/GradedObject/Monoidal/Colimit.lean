/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import ReasLib.CategoryTheory.GradedObject.Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits and tensor products of graded objects

The total tensor product of graded objects is assembled from coproducts of ambient tensor
products.  Cocontinuity of ambient tensoring therefore lifts to cocontinuity of graded tensoring.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v w w' z

namespace CategoryTheory.GradedObject.Monoidal

variable {C : Type u} [Category.{v} C] {I : Type z} [AddMonoid I]
variable [MonoidalCategory C] [MonoidalCategory (GradedObject I C)]

section Size

variable [HasColimitsOfSize.{w', w} C]
variable [∀ X : C, PreservesColimitsOfSize.{w', w} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{w', w} (MonoidalCategory.tensorRight X)]

/-- Tensoring graded objects on the left preserves every colimit in a fixed universe range when
ambient tensoring does. -/
@[stacks 0FPB "left graded tensor preserves sized colimits", instance]
theorem tensorLeftPreservesColimitsOfSize (G : GradedObject I C) :
    PreservesColimitsOfSize.{w', w} (MonoidalCategory.tensorLeft G) := sorry

/-- Tensoring graded objects on the right preserves every colimit in a fixed universe range when
ambient tensoring does. -/
@[stacks 0FPB "right graded tensor preserves sized colimits", instance]
theorem tensorRightPreservesColimitsOfSize (G : GradedObject I C) :
    PreservesColimitsOfSize.{w', w} (MonoidalCategory.tensorRight G) := sorry

end Size

end CategoryTheory.GradedObject.Monoidal

end
