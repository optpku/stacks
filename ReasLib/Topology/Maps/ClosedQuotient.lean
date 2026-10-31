/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed quotient maps

Mathlib provides `IsOpenQuotientMap`, but not the symmetric predicate for
surjective continuous closed maps. This module supplies that small Prop bundle,
its conversion to Mathlib's `Topology.IsQuotientMap`, and the subset-transport
API that is not already owned by Mathlib.
-/

@[expose] public section

open Set Topology

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {T : Set Y}

/-- A closed quotient map is a surjective continuous closed map. It is equivalently a closed
map that is a quotient map. -/
@[stacks 0AAU "surjective continuous closed maps"]
structure IsClosedQuotientMap (f : X → Y) : Prop where
  /-- A closed quotient map is surjective. -/
  surjective : Function.Surjective f
  /-- A closed quotient map is continuous. -/
  continuous : Continuous f
  /-- A closed quotient map is closed. -/
  isClosedMap : IsClosedMap f

namespace IsClosedQuotientMap

/-- Lemma 5.6.5 (5), tag 0AAU: a closed quotient map is a quotient map. -/
@[stacks 0AAU "surjective continuous closed maps are quotient maps"]
theorem isQuotientMap (hf : IsClosedQuotientMap f) : Topology.IsQuotientMap f :=
  hf.isClosedMap.isQuotientMap hf.continuous hf.surjective

/-- A closed quotient map is equivalently a closed map that is a quotient map. -/
theorem iff_isClosedMap_isQuotientMap :
    IsClosedQuotientMap f ↔ IsClosedMap f ∧ Topology.IsQuotientMap f := by
  constructor
  · intro hf
    exact ⟨hf.isClosedMap, hf.isQuotientMap⟩
  · rintro ⟨hclosed, hquotient⟩
    exact ⟨hquotient.surjective, hquotient.continuous, hclosed⟩

/-- Construct a closed quotient map from a closed map and a quotient map. -/
theorem of_isClosedMap_isQuotientMap (hclosed : IsClosedMap f) (hquotient : Topology.IsQuotientMap f) :
    IsClosedQuotientMap f :=
  iff_isClosedMap_isQuotientMap.mpr ⟨hclosed, hquotient⟩

/-- The identity is a closed quotient map. -/
protected theorem id : IsClosedQuotientMap (id : X → X) :=
  ⟨fun x => ⟨x, rfl⟩, continuous_id, IsClosedMap.id⟩

/-- Closed quotient maps are closed under composition. -/
theorem comp {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hg : IsClosedQuotientMap g) (hf : IsClosedQuotientMap f) :
    IsClosedQuotientMap (g ∘ f) :=
  ⟨hg.surjective.comp hf.surjective, hg.continuous.comp hf.continuous,
    hg.isClosedMap.comp hf.isClosedMap⟩

/-- Lemma 5.6.5 (1), tag 0AAU: a closed quotient map sends the closure of a preimage to the
closure of the original subset. -/
@[stacks 0AAU "closure as the image of the closure of the preimage"]
theorem closure_eq_image_closure_preimage (hf : IsClosedQuotientMap f) :
    closure T = f '' closure (f ⁻¹' T) := by
  calc
    closure T = closure (f '' (f ⁻¹' T)) := by rw [hf.surjective.image_preimage]
    _ = f '' closure (f ⁻¹' T) :=
      hf.isClosedMap.closure_image_eq_of_continuous hf.continuous _

/-- Lemma 5.6.5 (2), tag 0AAU: a closed quotient map reflects closed subsets along preimage. -/
theorem isClosed_iff_preimage (hf : IsClosedQuotientMap f) :
    IsClosed T ↔ IsClosed (f ⁻¹' T) :=
  hf.isQuotientMap.isCoinducing.isClosed_preimage.symm

/-- Lemma 5.6.5 (3), tag 0AAU: a closed quotient map reflects open subsets along preimage. -/
theorem isOpen_iff_preimage (hf : IsClosedQuotientMap f) :
    IsOpen T ↔ IsOpen (f ⁻¹' T) :=
  hf.isQuotientMap.isCoinducing.isOpen_preimage.symm

/-- Lemma 5.6.5 (4), tag 0AAU: a closed quotient map reflects locally closed subsets along
preimage. -/
@[stacks 0AAU "locally closed subsets are reflected by closed quotient preimage"]
theorem isLocallyClosed_iff_preimage (hf : IsClosedQuotientMap f) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  constructor
  · intro hT
    exact hT.preimage hf.continuous
  · intro hT
    rw [isLocallyClosed_iff_isOpen_coborder, coborder, isOpen_compl_iff] at hT ⊢
    rw [hf.closure_eq_image_closure_preimage, ← image_sdiff_preimage]
    exact hf.isClosedMap _ hT

end IsClosedQuotientMap

end
