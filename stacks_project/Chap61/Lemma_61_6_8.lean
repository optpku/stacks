/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.Retraction
import StacksCheckRecall

/-!
# Lemma 61.6.8

Every commutative ring admits a faithfully flat ind-Zariski extension whose
target satisfies the equivalent conditions of Lemma 61.6.7.
-/

universe u

/- Lemma 61.6.8: for a commutative ring `A`, there exists a faithfully flat
ind-Zariski ring map `f : A →+* B` such that `B` satisfies the equivalent
conditions of Lemma 61.6.7. -/
@[stacks 09B0] #check
  (RingHom.IndZariski.exists_faithfullyFlat_indZariskiRetraction :
    ∀ (A : Type u) [CommRing A],
      ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
        f.FaithfullyFlat ∧ f.IndZariski ∧ Algebra.HasFaithfullyFlatIndZariskiRetraction B)

/- There exists a faithfully flat ind-Zariski ring map `f : A →+* B` such that
`PrimeSpectrum B` is w-local and `ConnectedComponents (PrimeSpectrum B)` is
extremally disconnected. -/
#check
  (RingHom.IndZariski.exists_faithfullyFlat_wLocal_extremallyDisconnected :
    ∀ (A : Type u) [CommRing A],
      ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
        f.FaithfullyFlat ∧ f.IndZariski ∧
          WLocalSpace (PrimeSpectrum B) ∧
            ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum B)))
