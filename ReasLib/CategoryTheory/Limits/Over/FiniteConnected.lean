/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite connected limits in slice categories

Connected limits in a slice are created by its forgetful functor. Consequently the semantic
finite-connected-limit owner transfers from an ambient category to every slice category.
-/

@[expose] public section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C]

/-- A slice category has finite connected limits whenever its ambient category does. -/
@[stacks 08NJ "finite connected limits in slices"]
instance (priority := 100) hasFiniteConnectedLimits [HasFiniteConnectedLimits C] (X : C) :
    HasFiniteConnectedLimits (Over X) where
  out _ := CategoryTheory.Over.hasLimitsOfShape_of_isConnected

/-- The forgetful functor from a slice category preserves all finite connected limits. -/
@[stacks 08NJ "slice forgetful functor preserves finite connected limits"]
instance (priority := 100) Forget.preservesFiniteConnectedLimits (X : C) :
    PreservesFiniteConnectedLimits (Over.forget X) where
  out _ := CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected

/-- Preservation by a slice forgetful functor transfers across the canonical identity
`Over.map f ⋙ Over.forget Y ≅ Over.forget X`. -/
@[stacks 08NJ "slice map-forget preservation bridge"]
instance (priority := 100) mapForget.preservesLimitsOfShape
    {J : Type*} [Category J] {X Y : C} (f : X ⟶ Y)
    [PreservesLimitsOfShape J (Over.forget X)] :
    PreservesLimitsOfShape J (Over.map f ⋙ Over.forget Y) :=
  preservesLimitsOfShape_of_natIso (Over.mapForget f).symm

/-- Postcomposition between slice categories preserves all finite connected limits. -/
@[stacks 08NJ "slice postcomposition preserves finite connected limits"]
instance (priority := 100) Map.preservesFiniteConnectedLimits
    {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteConnectedLimits (Over.map f) where
  out _ := preservesLimitsOfShape_of_reflects_of_preserves
    (Over.map f) (Over.forget Y)

end CategoryTheory.Over
