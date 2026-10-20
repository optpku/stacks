/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Irreducible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps and Irreducible Components

This module specializes Mathlib's irreducible-component correspondence for
open maps to irreducible fibers and packages its useful computations.
-/

@[expose] public section

universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

namespace IsOpenMap

/-- Lemma 5.8.14: an open map over an irreducible target is irreducible when the points with
irreducible fibers form a dense set. -/
@[stacks 004Z]
theorem irreducibleSpace_of_dense_irreducibleFibers
    [IrreducibleSpace Y] (hopen : IsOpenMap f)
    (hdense : Dense {y : Y | IsIrreducible (f ⁻¹' {y})}) : IrreducibleSpace X := sorry

end IsOpenMap

/-- A map with irreducible fibers is surjective. -/
theorem surjective_of_irreducibleFibers
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) : Function.Surjective f := sorry

/-- Lemma 5.8.15: a continuous open map with irreducible fibers induces the canonical order
isomorphism from target irreducible components to source irreducible components. -/
@[stacks 037A]
def irreducibleComponentsEquivOfIrreducibleFibers
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y})) :
    irreducibleComponents Y ≃o irreducibleComponents X :=
  irreducibleComponentsEquivOfIsPreirreducibleFiber f hcont hopen
    (fun y ↦ (hfibers y).isPreirreducible)
    (surjective_of_irreducibleFibers hfibers)

/-- The source component corresponding to a target component is its inverse image. -/
@[simp]
theorem coe_irreducibleComponentsEquivOfIrreducibleFibers_apply
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y}))
    (Z : irreducibleComponents Y) :
    ((irreducibleComponentsEquivOfIrreducibleFibers hcont hopen hfibers Z :
        irreducibleComponents X) : Set X) = f ⁻¹' (Z : Set Y) := sorry

/-- The inverse component correspondence sends a source component to its image. -/
@[simp]
theorem coe_irreducibleComponentsEquivOfIrreducibleFibers_symm_apply
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsIrreducible (f ⁻¹' {y}))
    (Z : irreducibleComponents X) :
    (((irreducibleComponentsEquivOfIrreducibleFibers hcont hopen hfibers).symm Z :
        irreducibleComponents Y) : Set Y) = f '' (Z : Set X) := sorry
