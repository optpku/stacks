/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.AdicCompletion.Branches.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# One-dimensional branches of a completion

A one-dimensional minimal branch of the completion of a Noetherian local ring is the radical of
the extension of a minimal prime from any chosen henselization.

@stack 0C2B
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

namespace IsHenselizationOf.Completion.Comparison

/-- Lemma 15.109.5: a one-dimensional minimal prime of the completion of a Noetherian local ring
is the radical of the extension of a minimal prime of a chosen henselization. -/
@[stacks 0C2B "Lemma 15.109.5"]
theorem exists_minimalPrime_of_completion_quotient_dimension_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah))
    (q : minimalPrimes (AdicCompletion (maximalIdeal A) A))
    (hdim : ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ q.1) = 1) :
    ∃ qh : minimalPrimes Ah,
      (q : Ideal (AdicCompletion (maximalIdeal A) A)) =
        Ideal.radical (Ideal.map iota.toAlgHom.toRingHom qh) := sorry
-- Proof strategy: lift the contraction of `q` through `minimalPrimeMap_surjective`; the
-- one-dimensional quotient hypothesis forces `q` to be the unique minimal prime over the
-- extended ideal, hence equal to its radical.

end IsHenselizationOf.Completion.Comparison
