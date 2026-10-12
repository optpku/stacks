/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Pair.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products of pair Henselizations

This file owns the natural map from the Henselization of an intersection of ideals to the product
of their individual Henselizations.

@stack 0H7Q
-/

@[expose] public section

universe u v

noncomputable section

namespace RingPairCat

variable {A : Type u} [CommRing A]
variable {ι : Type v} [henselianPairInclusion.IsRightAdjoint]

/-- The natural map from the Henselization of `(⨅ i, I i)` to the product of the
Henselizations of the ideals `I i`. -/
@[stacks 0H7Q "natural product comparison for pair Henselization"]
def henselizationIntersectionToPi (I : ι → Ideal A) :
    henselizationRing (pairOfIdeal (⨅ j, I j)) →+*
      ∀ i : ι, henselizationRing (pairOfIdeal (I i)) :=
  RingHom.pi fun i ↦
    henselizationRingMap (pairOfIdealMap (⨅ j, I j) (I i) (iInf_le I i))

/-- Lemma 15.12.8: for a finite nonempty pairwise-comaximal family, the natural product
comparison on Henselization rings is bijective. -/
@[stacks 0H7Q "Lemma 15.12.8"]
theorem henselizationIntersectionToPi_bijective [Finite ι] [Nonempty ι]
    (I : ι → Ideal A) (hI : Pairwise fun i j ↦ IsCoprime (I i) (I j)) :
    Function.Bijective (henselizationIntersectionToPi I) := sorry

end RingPairCat
