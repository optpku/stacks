/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids.Objects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inertia objects of stacks in sets

Bundled relative and absolute inertia in `StackOver.Sets`, with direct discrete-fibration
membership and computation on the underlying set-fibred categories.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.StackOver.Sets

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Sets.{u, v, w, vS} J}

/-- Relative inertia of a morphism of stacks in sets has a discrete-fibration projection.

The proof applies the direct neutral set-fibred relative-inertia closure after identifying the
projection; it does not transport strict discreteness across the setoid inertia equivalence. -/
@[stacks 036Y "relative inertia set-stack discrete-fibration closure"]
theorem relativeInertia.isDiscreteFibration (F : X ⟶ Y) :
    Functor.IsDiscreteFibration
      (StackOver.Setoids.relativeInertia (Hom.toSetoidsMor F)).p := sorry

/-- Relative inertia of a morphism of stacks in sets, bundled in the strict set-fibred stack
owner. -/
@[stacks 036Y "relative inertia stack in sets"]
def relativeInertia (F : X ⟶ Y) :
    StackOver.Sets.{u, v, max w vS, vS} J :=
  ⟨StackOver.Setoids.relativeInertia (Hom.toSetoidsMor F),
    relativeInertia.isDiscreteFibration F⟩

/-- The set-fibred view of bundled relative inertia is the direct neutral set-fibred owner. -/
@[simp, stacks 036Y "relative inertia set-stack underlying computation"]
theorem relativeInertia.toSets (F : X ⟶ Y) :
    (relativeInertia F).toSets =
      FiberedCategoryOver.Sets.relativeInertia (Hom.toSetsMor F) := sorry

/-- Absolute inertia of a stack in sets has a discrete-fibration projection by direct neutral
closure. -/
@[stacks 036Y "absolute inertia set-stack discrete-fibration closure"]
theorem inertia.isDiscreteFibration (X : StackOver.Sets.{u, v, w, vS} J) :
    Functor.IsDiscreteFibration (StackOver.Setoids.inertia X.toSetoids).p := sorry

/-- Absolute inertia of a stack in sets, bundled in the strict set-fibred stack owner. -/
@[stacks 036Y "absolute inertia stack in sets"]
def inertia (X : StackOver.Sets.{u, v, w, vS} J) :
    StackOver.Sets.{u, v, max w vS, vS} J :=
  ⟨StackOver.Setoids.inertia X.toSetoids, inertia.isDiscreteFibration X⟩

/-- The set-fibred view of bundled stack inertia is the direct neutral set-fibred owner. -/
@[simp, stacks 036Y "absolute inertia set-stack underlying computation"]
theorem inertia.toSets (X : StackOver.Sets.{u, v, w, vS} J) :
    (inertia X).toSets = FiberedCategoryOver.Sets.inertia X.toSets := sorry

end CategoryTheory.StackOver.Sets
