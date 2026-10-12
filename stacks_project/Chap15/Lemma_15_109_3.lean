/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.Away.Idempotent.Descent
import StacksCheckRecall

/-!
# Lemma 15.109.3

@stack 0C2A
-/

@[expose] public section

universe u v

variable {A : Type u} {C : Type v} [CommRing A] [CommRing C]

/-! # Lemma 15.109.3: descent of complementary idempotent factors -/

/- Lemma 15.109.3, tag `0C2A`: idempotent localizations on the basic-open charts of a finitely
generated ideal admit one global quotient complement. -/
@[stacks 0C2A "Lemma 15.109.3"]
#check fun (f : A →+* C) (I : Ideal A) (hI : I.FG)
    (h_local : ∀ {a : A}, a ∈ I →
      (Localization.awayMap f a).IsIdempotentLocalization) ↦
  (RingHom.IsIdempotentLocalization.existsQuotientComplement f I hI h_local :
    ∃ J : Ideal A, ∀ {a : A}, a ∈ I →
      Function.Bijective
        (Localization.awayMap (f.prod (Ideal.Quotient.mk J)) a))
