/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.Open
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally closed and nowhere dense subsets under open quotient maps

This module complements mathlib's `IsOpenQuotientMap` API with the subset
properties that an open quotient map reflects.  Existing closure, open, closed,
and quotient-map APIs remain owned by mathlib.
-/

@[expose] public section

open Set Topology

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {T : Set Y}

namespace IsOpenQuotientMap

/-- Lemma 5.6.4 (1), tag 02YB: an open quotient map commutes with closure along preimage. -/
@[stacks 02YB "closure commutes with preimage"]
theorem preimage_closure_eq_closure_preimage (hf : IsOpenQuotientMap f) :
    f ⁻¹' closure T = closure (f ⁻¹' T) := sorry

/-- Lemma 5.6.4 (2), tag 02YB: an open quotient map reflects closed subsets along preimage. -/
@[stacks 02YB "closed subsets are reflected by preimage"]
theorem isClosed_iff_preimage (hf : IsOpenQuotientMap f) :
    IsClosed T ↔ IsClosed (f ⁻¹' T) := sorry

/-- Lemma 5.6.4 (3), tag 02YB: an open quotient map reflects open subsets along preimage. -/
@[stacks 02YB "open subsets are reflected by preimage"]
theorem isOpen_iff_preimage (hf : IsOpenQuotientMap f) :
    IsOpen T ↔ IsOpen (f ⁻¹' T) := sorry

/-- Lemma 5.6.4 (4), tag 02YB: an open quotient map reflects locally closed subsets along
preimage. -/
@[stacks 02YB "locally closed subsets are reflected by open quotient preimage"]
theorem isLocallyClosed_iff_preimage (hf : IsOpenQuotientMap f) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := sorry

/-- Lemma 5.21.6 (2), tag 03HR: an open quotient map reflects nowhere dense subsets along
preimage. -/
@[stacks 03HR "nowhere dense sets under open quotient preimage"]
theorem isNowhereDense_iff_preimage (hf : IsOpenQuotientMap f) :
    IsNowhereDense T ↔ IsNowhereDense (f ⁻¹' T) := sorry

/-- Lemma 5.21.6 (2), tag 03HR: an open quotient map reflects closed nowhere dense subsets along
preimage. -/
@[stacks 03HR "closed nowhere dense sets under open quotient preimage"]
theorem isClosed_isNowhereDense_iff_preimage (hf : IsOpenQuotientMap f) :
    IsClosed T ∧ IsNowhereDense T ↔
      IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T) := sorry

end IsOpenQuotientMap

end
