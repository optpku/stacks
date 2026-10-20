/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Properties of finite composable-arrow diagrams

The objects, successor maps, and component maps of a `ComposableArrows` diagram are the three
reusable interfaces needed by most finite-ladder arguments.  These definitions package the
corresponding pointwise predicates without introducing a new bundled diagram structure.
-/

open CategoryTheory

universe v u

namespace CategoryTheory
namespace ComposableArrows

variable {C : Type u} [Category.{v} C]

/-- A property of the successor maps of a finite composable-arrow diagram. -/
@[stacks 014M "successor-map property of a composable-arrow diagram"]
def arrowProperty {n : ℕ} (W : MorphismProperty C) :
    ObjectProperty (ComposableArrows C n) :=
  fun F ↦ ∀ i : Fin n, W (F.map' i.1 (i.1 + 1))

/-- A property of all objects in a finite composable-arrow diagram. -/
@[stacks 014M "object property of a composable-arrow diagram"]
def objectProperty {n : ℕ} (P : ObjectProperty C) :
    ObjectProperty (ComposableArrows C n) :=
  fun F ↦ ∀ i : Fin (n + 1), P (F.obj i)

/-- A property of all components of a morphism between finite composable-arrow diagrams. -/
@[stacks 014M "component property of a composable-arrow morphism"]
def componentProperty {n : ℕ} (W : MorphismProperty C) :
    MorphismProperty (ComposableArrows C n) :=
  fun _ _ φ ↦ ∀ i : Fin (n + 1), W (φ.app i)

/-- Unfolding the successor-map property exposes the canonical `Fin n` indexing. -/
@[simp]
theorem arrowProperty_iff {n : ℕ} (W : MorphismProperty C) (F : ComposableArrows C n) :
    arrowProperty W F ↔ ∀ i : Fin n, W (F.map' i.1 (i.1 + 1)) := sorry

/-- Unfolding the object property exposes the canonical `Fin (n + 1)` indexing. -/
@[simp]
theorem objectProperty_iff {n : ℕ} (P : ObjectProperty C) (F : ComposableArrows C n) :
    objectProperty P F ↔ ∀ i : Fin (n + 1), P (F.obj i) := sorry

/-- Unfolding the component property exposes the canonical component indexing. -/
@[simp]
theorem componentProperty_iff {n : ℕ} (W : MorphismProperty C)
    {F G : ComposableArrows C n} (φ : F ⟶ G) :
    componentProperty W φ ↔ ∀ i : Fin (n + 1), W (φ.app i) := sorry

end ComposableArrows
end CategoryTheory
