module

public import ReasLib.RingTheory.Etale.Noetherian
import StacksCheckRecall

/-!
# Lemma 15.44.1

@stack 0AGZ
-/

@[expose] public section

universe u v

/- Lemma 15.44.1: Noetherianity is equivalent for the local rings at a prime of an etale algebra
and its contraction. -/
@[stacks 0AGZ "Lemma 15.44.1"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (q : PrimeSpectrum B) ↦
  (Algebra.Etale.localizationAtPrime_isNoetherianRing_iff q :
    IsNoetherianRing (Localization.AtPrime (q.asIdeal.under A)) ↔
      IsNoetherianRing (Localization.AtPrime q.asIdeal))
