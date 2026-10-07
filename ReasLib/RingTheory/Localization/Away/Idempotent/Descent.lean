module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Away.Idempotent

@[expose] public section

/-!
# Descent of complementary factors from idempotent localization charts

@stack 0C2A

A finitely generated ideal gives a finite basic-open cover. If a ring map is an idempotent
localization on every chart in that cover, the complementary idempotents descend to one quotient
of the source ring. The conclusion uses the canonical quotient rather than an unstructured
surjective ring map.
-/

universe u v

namespace RingHom.IsIdempotentLocalization

variable {A : Type u} {C : Type v} [CommRing A] [CommRing C]

/-- Lemma 15.109.3 (Tag `0C2A`): if `I` is finitely generated and `A_f → C_f` is an
idempotent localization for every `f ∈ I`, then a quotient `A ⨸ J` supplies a complementary
factor such that `A_f → (C × A ⨸ J)_f` is bijective for every `f ∈ I`. -/
@[stacks 0C2A "descent of complementary idempotent factors"]
theorem existsQuotientComplement (f : A →+* C) (I : Ideal A) (hI : I.FG)
    (h_local : ∀ {a : A}, a ∈ I →
      (Localization.awayMap f a).IsIdempotentLocalization) :
    ∃ J : Ideal A, ∀ {a : A}, a ∈ I →
      Function.Bijective
        (Localization.awayMap (f.prod (Ideal.Quotient.mk J)) a) := sorry
-- Proof strategy: choose a finite generating family for `I`, descend the complementary
-- idempotent on each basic-open chart, and combine the finitely many complements into one
-- quotient ideal `J`; localization then identifies every product map with the local splitting.

end RingHom.IsIdempotentLocalization
