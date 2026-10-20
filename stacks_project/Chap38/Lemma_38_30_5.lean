/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.IdealFactorization
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 38.30.5: an ideal of finite type in an étale algebra, supported over the
zero locus of a regular element, locally factors over every prime as the extension of
an ideal of finite type from the base times another ideal of finite type. -/
@[stacks 0813]
#check (Algebra.Etale.exists_away_factor :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (a : A) (h_regular : IsRegular a) (J : Ideal B) (hJ : J.FG)
    (hV : PrimeSpectrum.zeroLocus (J : Set B) ⊆
      PrimeSpectrum.zeroLocus ({algebraMap A B a} : Set B)) (q : PrimeSpectrum B),
    ∃ (I : Ideal A) (g : B) (J' : Ideal (Localization.Away g)),
      I.FG ∧ PrimeSpectrum.zeroLocus (I : Set A) ⊆
          PrimeSpectrum.zeroLocus ({a} : Set A) ∧
        g ∉ q.asIdeal ∧ J'.FG ∧
          Ideal.map (algebraMap A (Localization.Away g)) I =
            Ideal.map (algebraMap B (Localization.Away g)) J * J')
