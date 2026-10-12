/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsoluteTransformations.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Stable
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inertia objects of stacks in setoids

Bundled relative and absolute inertia objects in `StackOver.Setoids`, together with the
setoid-fibre closure facts used by their constructors.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.StackOver.Setoids

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Setoids.{u, v, w, vS} J}

/-- Relative inertia of a setoid-stack morphism has setoid fibres. -/
@[stacks 036Y "relative inertia setoid-stack closure"]
theorem relativeInertia.isFiberedInSetoids (F : X ⟶ Y) :
    Functor.IsFibered.InSetoids
      (StackOver.Groupoids.relativeInertia (Hom.toGroupoidsMor F)).p := sorry

/-- Relative inertia of a morphism of stacks in setoids, bundled as a stack in setoids. -/
@[stacks 036Y "relative inertia stack in setoids"]
def relativeInertia (F : X ⟶ Y) :
    StackOver.Setoids.{u, v, max w vS, vS} J :=
  ⟨StackOver.Groupoids.relativeInertia (Hom.toGroupoidsMor F),
    relativeInertia.isFiberedInSetoids F⟩

/-- Absolute inertia of a stack in setoids has setoid fibres. -/
@[stacks 036Y "absolute inertia setoid-stack closure"]
theorem inertia.isFiberedInSetoids (X : StackOver.Setoids.{u, v, w, vS} J) :
    Functor.IsFibered.InSetoids (StackOver.Groupoids.inertia X.toGroupoids).p := sorry

/-- Absolute inertia of a stack in setoids, bundled as a stack in setoids. -/
@[stacks 036Y "absolute inertia stack in setoids"]
def inertia (X : StackOver.Setoids.{u, v, w, vS} J) :
    StackOver.Setoids.{u, v, max w vS, vS} J :=
  ⟨StackOver.Groupoids.inertia X.toGroupoids, inertia.isFiberedInSetoids X⟩

end CategoryTheory.StackOver.Setoids
