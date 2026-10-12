/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
@stack 018N

# Finite (co)limit Kan-extension instances

This leaf owns the canonical pointwise Kan-extension instances along truncated-simplex
inclusions in categories with finite limits or finite colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace SimplexCategory.Truncated

variable {C : Type u} [Category.{v} C]

namespace inclusion.pointwise.left

/-- Finite colimits give pointwise left Kan extensions along the opposite truncated-simplex
inclusion, hence the coefficient-category input required by skeletons. -/
@[stacks 018N "truncated-simplex pointwise left Kan extension"]
instance kanExtension
    [HasFiniteColimits C] {m : ℕ} (F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C) :
    (inclusion m).op.HasPointwiseLeftKanExtension F :=
  fun ⟨⟨_⟩⟩ ↦ inferInstance

end inclusion.pointwise.left

namespace inclusion.pointwise.right

/-- Finite limits give pointwise right Kan extensions along the opposite truncated-simplex
inclusion, hence the coefficient-category input required by coskeletons. -/
@[stacks 0183 "truncated-simplex pointwise right Kan extension"]
instance kanExtension
    [HasFiniteLimits C] {m : ℕ} (F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C) :
    (inclusion m).op.HasPointwiseRightKanExtension F :=
  fun ⟨⟨_⟩⟩ ↦ inferInstance

end inclusion.pointwise.right

end SimplexCategory.Truncated
