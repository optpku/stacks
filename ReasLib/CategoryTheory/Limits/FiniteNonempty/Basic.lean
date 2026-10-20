/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite nonempty limits and colimits

This leaf owns the universe-stable existence classes and their basic shape projections.
Explicit product constructions live in `FiniteNonempty.Products`; construction criteria are
separated into `FiniteNonempty.Criteria`.
-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

/-- A discrete category is nonempty whenever its type of objects is nonempty. -/
instance Discrete.instNonempty {α : Type w} [Nonempty α] : Nonempty (Discrete α) := sorry

end CategoryTheory

namespace CategoryTheory.Limits

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category has finite nonempty limits if it has limits of every finite nonempty diagram. -/
@[stacks 04AU "finite nonempty limits"]
class HasFiniteNonemptyLimits : Prop where
  /-- A finite nonempty shape admits limits in the ambient category. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    HasLimitsOfShape J C

namespace HasFiniteNonemptyLimits

/-- A category with finite nonempty limits has limits of each finite nonempty shape. -/
instance (priority := 95) hasLimitsOfShape
    [HasFiniteNonemptyLimits C] (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    HasLimitsOfShape J C := sorry

/-- If `C` has limits of a fixed size, then it has finite nonempty limits. -/
theorem ofLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteNonemptyLimits C := sorry

/-- Construct finite nonempty limits by supplying them in any one universe. -/
theorem ofSize
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
      HasLimitsOfShape J C) :
    HasFiniteNonemptyLimits C := sorry

/-- A category has finite nonempty limits if and only if it has limits of every finite nonempty
shape in any fixed universe. -/
theorem iff_hasLimitsOfShape :
    HasFiniteNonemptyLimits C ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
        HasLimitsOfShape J C := sorry

/-- Finite limits are in particular finite nonempty limits. -/
instance ofHasFiniteLimits [HasFiniteLimits C] :
    HasFiniteNonemptyLimits C := sorry

/-- Finite nonempty limits include finite connected limits. -/
instance (priority := 90) hasFiniteConnectedLimits [HasFiniteNonemptyLimits C] :
    HasFiniteConnectedLimits C := sorry

end HasFiniteNonemptyLimits

/-- A category has finite nonempty colimits if it has colimits of every finite nonempty diagram. -/
@[stacks 04AW "finite nonempty colimits"]
class HasFiniteNonemptyColimits : Prop where
  /-- A finite nonempty shape admits colimits in the ambient category. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    HasColimitsOfShape J C

namespace HasFiniteNonemptyColimits

/-- A category with finite nonempty colimits has colimits of each finite nonempty shape. -/
instance (priority := 95) hasColimitsOfShape
    [HasFiniteNonemptyColimits C] (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    HasColimitsOfShape J C := sorry

/-- If `C` has colimits of a fixed size, then it has finite nonempty colimits. -/
theorem ofColimitsOfSize [HasColimitsOfSize.{v', u'} C] :
    HasFiniteNonemptyColimits C := sorry

/-- Construct finite nonempty colimits by supplying them in any one universe. -/
theorem ofSize
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
      HasColimitsOfShape J C) :
    HasFiniteNonemptyColimits C := sorry

/-- A category has finite nonempty colimits if and only if it has colimits of every finite
nonempty shape in any fixed universe. -/
theorem iff_hasColimitsOfShape :
    HasFiniteNonemptyColimits C ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
        HasColimitsOfShape J C := sorry

/-- Finite colimits are in particular finite nonempty colimits. -/
instance ofHasFiniteColimits [HasFiniteColimits C] :
    HasFiniteNonemptyColimits C := sorry

/-- Finite nonempty colimits include finite connected colimits. -/
instance (priority := 90) hasFiniteConnectedColimits [HasFiniteNonemptyColimits C] :
    HasFiniteConnectedColimits C := sorry

/-- Finite nonempty colimits in `C` are finite nonempty limits in `Cᵒᵖ`. -/
theorem iff_limits_op :
    HasFiniteNonemptyColimits C ↔ HasFiniteNonemptyLimits Cᵒᵖ := sorry

/-- Finite nonempty colimits in `C` give finite nonempty limits in `Cᵒᵖ`. -/
theorem op [HasFiniteNonemptyColimits C] : HasFiniteNonemptyLimits Cᵒᵖ := sorry

/-- Finite nonempty colimits in `Cᵒᵖ` give finite nonempty limits in `C`. -/
theorem unop [HasFiniteNonemptyColimits Cᵒᵖ] : HasFiniteNonemptyLimits C := sorry

end HasFiniteNonemptyColimits

namespace HasFiniteNonemptyLimits

/-- Finite nonempty limits in `C` are finite nonempty colimits in `Cᵒᵖ`. -/
theorem iff_colimits_op :
    HasFiniteNonemptyLimits C ↔ HasFiniteNonemptyColimits Cᵒᵖ := sorry

/-- Finite nonempty limits in `C` give finite nonempty colimits in `Cᵒᵖ`. -/
theorem op [HasFiniteNonemptyLimits C] : HasFiniteNonemptyColimits Cᵒᵖ := sorry

/-- Finite nonempty limits in `Cᵒᵖ` give finite nonempty colimits in `C`. -/
theorem unop [HasFiniteNonemptyLimits Cᵒᵖ] : HasFiniteNonemptyColimits C := sorry

end HasFiniteNonemptyLimits

end CategoryTheory.Limits


