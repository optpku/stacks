/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sober
public import ReasLib.Topology.LocallyClosed.FiniteUnion

/-!
# Finite Locally Closed Traces on Irreducible Sets

This module records the dense-trace API for finite unions of locally closed
subsets of an irreducible subspace.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-- The trace of a finite union of locally closed subsets on an irreducible set is dense exactly
when it contains an open dense subtrace. -/
@[stacks 005K "open-dense trace criterion"]
theorem IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} (hZ : IsIrreducible Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    (∃ U : Opens Z, Dense (U : Set Z) ∧ (U : Set Z) ⊆ Z ↓∩ E) ↔ Dense (Z ↓∩ E) := sorry

/-- A finite union of locally closed subsets has dense trace on the subset owned by a generic
point exactly when that generic point belongs to the subset. -/
@[stacks 005K "generic-point membership criterion"]
theorem IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} {x : X} (hx : IsGenericPoint x Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    Dense (Z ↓∩ E) ↔ x ∈ E := sorry

/-- The explicit irreducible-set presentation of the generic-point dense trace criterion. -/
@[stacks 005K "generic-point membership criterion"]
theorem IsIrreducible.dense_preimage_iff_mem_of_isGenericPoint_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} {x : X} (hZ : IsIrreducible Z) (hx : IsGenericPoint x Z)
    (hE : IsFiniteUnionOfLocallyClosed E) :
    Dense (Z ↓∩ E) ↔ x ∈ E := sorry
