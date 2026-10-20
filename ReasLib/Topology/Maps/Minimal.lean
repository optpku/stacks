/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Hausdorff
public import ReasLib.Topology.Separation.Cardinal

/-!
# Minimal surjections

The condition that no proper closed subset of the source still maps onto the target occurs in
Gleason-style arguments and in cardinal bounds for covers.  It is bundled with surjectivity, but
not with continuity: continuity is an independent hypothesis of consumers that need it.
-/

@[expose] public section

universe u v

open Cardinal Function Set

/-- A surjection that does not remain surjective after restriction to any proper closed subset of
its source. -/
@[stacks 08YL "minimal surjections"]
structure IsMinimalSurjective {X : Type u} {Y : Type v} [TopologicalSpace X]
    (f : X → Y) : Prop where
  /-- The map is surjective. -/
  surjective : Surjective f
  /-- No proper closed subset of the source maps onto the target. -/
  image_ne_univ_of_proper_isClosed (Z : Set X) (hZ : Z ≠ univ) (hZclosed : IsClosed Z) :
    f '' Z ≠ univ

/-- The explicit surjectivity and proper-closed-image characterization of a minimal surjection. -/
@[stacks 08YL "characterization of minimal surjections"]
theorem isMinimalSurjective_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    {f : X → Y} :
    IsMinimalSurjective f ↔
      Surjective f ∧
        ∀ Z : Set X, Z ≠ univ → IsClosed Z → f '' Z ≠ univ := sorry

namespace IsMinimalSurjective

variable {X : Type u} {Y : Type v} [TopologicalSpace X] {f : X → Y}

/-- The canonical right inverse of a minimal surjection has dense range. -/
@[stacks 08YL "dense canonical section of a minimal surjection"]
theorem denseRange_surjInv (h : IsMinimalSurjective f) :
    DenseRange (surjInv h.surjective) := sorry

/-- A minimal surjection from a Hausdorff space satisfies the double-power cardinal bound induced
by the dense range of its canonical section. -/
@[stacks 0909 "cardinal bound for a minimal surjection"]
theorem cardinalMk_le_doublePower [T2Space X] (h : IsMinimalSurjective f)
    (κ : Cardinal.{max u v}) (hκY : Cardinal.lift (Cardinal.mk Y) ≤ κ) :
    Cardinal.lift (Cardinal.mk X) ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ κ) := sorry

end IsMinimalSurjective
