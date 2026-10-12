/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Locally finite sums of algebraic cycles

This file constructs pointwise sums of locally finite families of algebraic cycles.
-/

@[expose] public section

open Function Set Topology TopologicalSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Type u} [TopologicalSpace X]
variable {R : Type v} [AddCommMonoid R]
variable {ι : Type w}

/-- The pointwise sum of a locally finite family of functions with locally finite support again
has locally finite support. -/
theorem locallyFiniteSum_locallyFiniteSupport
    (c : ι → Function.locallyFinsupp X R)
    (hc : LocallyFinite fun i ↦ (c i).support) :
    LocallyFiniteSupport (fun x ↦ ∑ᶠ i, c i x) := sorry

/-- The pointwise sum of a locally finite family of locally supported functions. -/
noncomputable def locallyFiniteSum
    (c : ι → Function.locallyFinsupp X R)
    (hc : LocallyFinite fun i ↦ (c i).support) :
    Function.locallyFinsupp X R :=
  { toFun := fun x ↦ ∑ᶠ i, c i x
    supportWithinDomain' := Set.subset_univ _
    supportLocallyFiniteWithinDomain' :=
      fun x _ ↦ locallyFiniteSum_locallyFiniteSupport c hc x }

/-- Evaluation of a locally finite sum is the corresponding pointwise finite sum. -/
theorem locallyFiniteSum_apply
    (c : ι → Function.locallyFinsupp X R)
    (hc : LocallyFinite fun i ↦ (c i).support) (x : X) :
    locallyFiniteSum c hc x = ∑ᶠ i, c i x := sorry

end AlgebraicGeometry.AlgebraicCycle
