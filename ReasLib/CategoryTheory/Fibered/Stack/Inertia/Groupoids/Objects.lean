/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Basic.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inertia objects of stacks in groupoids

Bundled relative and absolute inertia objects in `StackOver.Groupoids`, together with the
closure facts needed by their constructors.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.StackOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Groupoids.{u, v, w, vS} J}

/-- The groupoid-fibred relative-inertia carrier satisfies the stack condition. -/
@[stacks 036Y "relative inertia groupoid-stack closure"]
theorem relativeInertia.isStackOnSite (F : X ⟶ Y) :
    IsStack.OnSite J
      (FiberedCategoryOver.Groupoids.relativeInertia (Hom.toGroupoidsMor F)).p := sorry

/-- Relative inertia of a morphism of stacks in groupoids, bundled as a stack in groupoids. -/
@[stacks 036Y "relative inertia stack in groupoids"]
def relativeInertia (F : X ⟶ Y) :
    StackOver.Groupoids.{u, v, max w vS, vS} J :=
  ⟨FiberedCategoryOver.Groupoids.relativeInertia (Hom.toGroupoidsMor F),
    relativeInertia.isStackOnSite F⟩

/-- The groupoid-fibred absolute-inertia carrier satisfies the stack condition. -/
@[stacks 036Y "absolute inertia groupoid-stack closure"]
theorem inertia.isStackOnSite (X : StackOver.Groupoids.{u, v, w, vS} J) :
    IsStack.OnSite J (FiberedCategoryOver.Groupoids.inertia X.toGroupoids).p := sorry

/-- Absolute inertia of a stack in groupoids, bundled as a stack in groupoids. -/
@[stacks 036Y "absolute inertia stack in groupoids"]
def inertia (X : StackOver.Groupoids.{u, v, w, vS} J) :
    StackOver.Groupoids.{u, v, max w vS, vS} J :=
  ⟨FiberedCategoryOver.Groupoids.inertia X.toGroupoids, inertia.isStackOnSite X⟩

end CategoryTheory.StackOver.Groupoids
