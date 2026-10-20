/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Constructible.Subspace

/-!
# Locality of Constructible Sets

Constructibility can be checked on finite retrocompact open covers and finite
constructible families.
-/

@[expose] public section

universe u v

open Set TopologicalSpace
open scoped Set.Notation

namespace TopologicalSpace.IsOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.15.6: constructibility is local on a finite retrocompact open
cover. -/
@[stacks 053W]
theorem isConstructible_iff_preimage_of_finite_retrocompact
    {ι : Type v} [Finite ι] {V : ι → Opens X} (hV : IsOpenCover V)
    (hretro : ∀ i, IsRetrocompact (V i : Set X)) {E : Set X} :
    Topology.IsConstructible E ↔ ∀ i, Topology.IsConstructible ((V i : Set X) ↓∩ E) := sorry

end TopologicalSpace.IsOpenCover

namespace Topology.IsConstructible

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X]

/-- Constructibility can be checked on a finite constructible family covering
the subset under consideration. -/
theorem iff_of_finiteFamily
    {ι : Type v} [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsConstructible (Z i))
    {E : Set X} (hcover : E ⊆ ⋃ i, Z i) :
    IsConstructible E ↔ ∀ i, IsConstructible (Z i ↓∩ E) := sorry

/-- Lemma 5.15.14: constructibility is local on a finite constructible cover
of the ambient space. -/
@[stacks 09YK]
theorem iff_of_finiteCover
    {ι : Type v} [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsConstructible (Z i))
    {E : Set X} (hcover : (univ : Set X) = ⋃ i, Z i) :
    IsConstructible E ↔ ∀ i, IsConstructible (Z i ↓∩ E) := sorry

end Topology.IsConstructible
