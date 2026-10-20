/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventual degeneracy of simplicial sets

This file packages the existence of a finite dimension bound as a named simplicial-set property.
It replaces anonymous `Fact` wrappers while retaining bridges to Mathlib's concrete
`SSet.HasDimensionLE` classes.
-/

@[expose] public section

open CategoryTheory Simplicial

universe u

namespace SSet

/-- A simplicial set is eventually degenerate if it has some finite dimension bound. -/
@[stacks 017K, stacks 017L, stacks 018V "eventual degeneracy of a simplicial set"]
protected class EventuallyDegenerate (X : SSet.{u}) : Prop where
  /-- An eventual-degeneracy witness is a dimension bound. -/
  exists_bound : ∃ d : ℕ, X.HasDimensionLE d

namespace EventuallyDegenerate

/-- A specified dimension bound implies eventual degeneracy. -/
@[stacks 018V "eventual degeneracy from a dimension bound"]
theorem ofBound (X : SSet.{u}) (d : ℕ) [X.HasDimensionLE d] :
    X.EventuallyDegenerate := sorry

/-- A finite simplicial set is eventually degenerate. -/
@[stacks 018V "finite simplicial sets are eventually degenerate"]
instance (priority := 50) ofFinite (X : SSet.{u}) [X.Finite] :
    X.EventuallyDegenerate := sorry

/-- An existential dimension bound can be bundled as eventual degeneracy. -/
@[stacks 017K, stacks 017L "bundle an eventual dimension bound"]
theorem ofExists {X : SSet.{u}} (h : ∃ d : ℕ, X.HasDimensionLE d) :
    X.EventuallyDegenerate := sorry

/-- Eventual degeneracy passes to the domain of a monomorphism. -/
@[stacks 017K, stacks 017L, stacks 018V "eventual degeneracy under monomorphisms"]
theorem ofMono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    [Y.EventuallyDegenerate] : X.EventuallyDegenerate := sorry

/-- Eventual degeneracy passes to the codomain of an epimorphism. -/
@[stacks 017K, stacks 017L, stacks 018V "eventual degeneracy under epimorphisms"]
theorem ofEpi {X Y : SSet.{u}} (f : X ⟶ Y) [Epi f]
    [X.EventuallyDegenerate] : Y.EventuallyDegenerate := sorry

/-- Eventual degeneracy transports across an isomorphism. -/
@[stacks 017K, stacks 017L, stacks 018V "eventual degeneracy under isomorphisms"]
theorem ofIso {X Y : SSet.{u}} (e : X ≅ Y) [X.EventuallyDegenerate] :
    Y.EventuallyDegenerate := sorry

/-- Isomorphic simplicial sets are eventually degenerate simultaneously. -/
@[stacks 017K, stacks 017L, stacks 018V "eventual degeneracy isomorphism criterion"]
theorem iffOfIso {X Y : SSet.{u}} (e : X ≅ Y) :
    X.EventuallyDegenerate ↔ Y.EventuallyDegenerate := sorry

end EventuallyDegenerate

/-- Every subcomplex of an eventually degenerate simplicial set is eventually degenerate. -/
@[stacks 017K, stacks 017L, stacks 018V "eventual degeneracy of subcomplexes"]
instance Subcomplex.eventuallyDegenerate {X : SSet.{u}} [X.EventuallyDegenerate]
    (A : X.Subcomplex) : SSet.EventuallyDegenerate (A : SSet.{u}) := sorry

/-- Eventual degeneracy is equivalent to the existence of a finite dimension bound. -/
@[stacks 017K, stacks 017L, stacks 018V "eventual degeneracy criterion"]
theorem eventuallyDegenerate_iff (X : SSet.{u}) :
    X.EventuallyDegenerate ↔ ∃ d : ℕ, X.HasDimensionLE d := sorry

end SSet
