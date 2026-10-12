/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.Pair.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pair Henselization of a local ring

The pair Henselization of `(A, maximalIdeal A)` is the canonical local-ring Henselization of `A`.

@stack 0A03
-/

@[expose] public section

open IsLocalRing
open RingPairCat

universe u

noncomputable section

/-- Local instance justification (instance diamond): select the canonical right-adjoint witness
for the inclusion of henselian pairs only in this local-ring specialization. -/
local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- Lemma 15.12.3: the pair Henselization of `(A, maximalIdeal A)` is a Henselization of the
local ring `A`. -/
@[stacks 0A03 "Lemma 15.12.3"]
theorem localRing_henselization_isHenselizationOf
    (A : Type u) [CommRing A] [IsLocalRing A] :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) := sorry

namespace localRing_henselization

/-- The pair Henselization of a local ring is available as the canonical `IsHenselizationOf`
instance. -/
@[stacks 0A03 "canonical local-ring Henselization instance"]
instance instIsHenselizationOf (A : Type u) [CommRing A] [IsLocalRing A] :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) := sorry

end localRing_henselization
