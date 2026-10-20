/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.Etale.LocalStructure
import StacksCheckRecall

universe u v

/- Theorem 41.12.1: an essentially étale local homomorphism of local rings factors
through a standard étale algebra and a localization at a prime. -/
@[stacks 025B] #check
  (RingHom.EssEtale.exists_standardEtale_localizationAtPrime :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] {φ : A →+* B} [IsLocalHom φ],
      φ.EssEtale →
        ∃ (P : StandardEtalePair A) (q : Ideal P.Ring) (_ : q.IsPrime)
          (ψ : P.Ring →+* B),
          q.primeCompl.IsLocalizationMap ψ ∧
            φ = ψ.comp (algebraMap A P.Ring))
