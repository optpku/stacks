/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
theorem isQuotientMap (hf : IsClosedQuotientMap f) : Topology.IsQuotientMap f := sorry

/-- A closed quotient map is equivalently a closed map that is a quotient map. -/
theorem iff_isClosedMap_isQuotientMap :
    IsClosedQuotientMap f ↔ IsClosedMap f ∧ Topology.IsQuotientMap f := sorry

/-- Construct a closed quotient map from a closed map and a quotient map. -/
theorem of_isClosedMap_isQuotientMap (hclosed : IsClosedMap f) (hquotient : Topology.IsQuotientMap f) :
    IsClosedQuotientMap f := sorry

/-- The identity is a closed quotient map. -/
protected theorem id : IsClosedQuotientMap (id : X → X) := sorry

/-- Closed quotient maps are closed under composition. -/
theorem comp {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hg : IsClosedQuotientMap g) (hf : IsClosedQuotientMap f) :
    IsClosedQuotientMap (g ∘ f) := sorry

/-- Lemma 5.6.5 (1), tag 0AAU: a closed quotient map sends the closure of a preimage to the
closure of the original subset. -/
theorem closure_eq_image_closure_preimage (hf : IsClosedQuotientMap f) :
    closure T = f '' closure (f ⁻¹' T) := sorry

/-- Lemma 5.6.5 (2), tag 0AAU: a closed quotient map reflects closed subsets along preimage. -/
theorem isClosed_iff_preimage (hf : IsClosedQuotientMap f) :
    IsClosed T ↔ IsClosed (f ⁻¹' T) := sorry

/-- Lemma 5.6.5 (3), tag 0AAU: a closed quotient map reflects open subsets along preimage. -/
theorem isOpen_iff_preimage (hf : IsClosedQuotientMap f) :
    IsOpen T ↔ IsOpen (f ⁻¹' T) := sorry

/-- Lemma 5.6.5 (4), tag 0AAU: a closed quotient map reflects locally closed subsets along
preimage. -/
theorem isLocallyClosed_iff_preimage (hf : IsClosedQuotientMap f) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := sorry

end IsClosedQuotientMap

namespace Topology.IsQuotientMap

/-- Lemma 5.6.5 (1), tag 0AAU: a closed quotient map sends the closure of a preimage to the
closure of the original subset. -/
@[stacks 0AAU "closure as the image of the closure of the preimage"]
theorem closure_eq_image_closure_preimage (hf : IsQuotientMap f) (hclosed : IsClosedMap f) :
    closure T = f '' closure (f ⁻¹' T) := sorry

/-- Lemma 5.6.5 (4), tag 0AAU: a closed quotient map reflects locally closed subsets along
preimage. -/
@[stacks 0AAU "locally closed subsets are reflected by closed quotient preimage"]
theorem isLocallyClosed_iff_preimage (hf : IsQuotientMap f) (hclosed : IsClosedMap f) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := sorry

end Topology.IsQuotientMap

end
