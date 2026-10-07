module

public import ReasLib.Algebra.IndEtaleEnvelope.Cardinality
import StacksCheckRecall

@[expose] public section

universe u

open scoped Cardinal
open Algebra.IndEtaleEnvelope

/- Remark 61.8.2 (1): if `A` is a ring and `κ` is an infinite cardinal with
`#A ≤ κ`, then the cardinality of `T(A) = IndEtaleEnvelope A` is at most `κ`. -/
@[stacks 097S] #check
  (Algebra.IndEtaleEnvelope.mk_le :
    ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
      #(Algebra.IndEtaleEnvelope A) ≤ κ)

/- Remark 61.8.2 (2): if `A` is a ring and `κ` is an infinite cardinal with
`#A ≤ κ`, then the ring constructed in the proof of Lemma 61.8.1, namely
`Iteration A`, has cardinality at most `κ`. -/
@[stacks 097S] #check
  (Algebra.IndEtaleEnvelope.mk_iteration_le :
    ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
      #(Algebra.IndEtaleEnvelope.Iteration A) ≤ κ)
