/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Independence
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.17.4: if positive powers of generators of the maximal ideal of a local ring
are independent, then the length of their quotient is the product of the exponents. -/
@[stacks 0EBY]
#check (RingTheory.Sequence.IsIndependent.length_quotient_pow :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] {n : ℕ}
    (x : Fin n → A) (e : Fin n → ℕ)
    (h_span : IsLocalRing.maximalIdeal A = Ideal.span (Set.range x))
    (h_pos : ∀ i, 0 < e i)
    (h_independent : RingTheory.Sequence.IsIndependent (fun i ↦ x i ^ e i)),
    Module.length A (A ⧸ Ideal.span (Set.range (fun i ↦ x i ^ e i))) =
      ∏ i, (e i : ℕ∞))
