/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.WLocalHull.AlongClosed
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.5.7. A profinite closed locus admits an ind-Zariski extension with
w-local spectrum, closed points V(IB), and canonical quotient isomorphism. -/
@[stacks 0979] #check (Algebra.WLocalHull.exists_alongClosed :
  ∀ (A : Type u) [CommRing A] (I : Ideal A)
    [CompactSpace (PrimeSpectrum.zeroLocus (I : Set A))]
    [T2Space (PrimeSpectrum.zeroLocus (I : Set A))]
    [TotallyDisconnectedSpace (PrimeSpectrum.zeroLocus (I : Set A))],
    ∃ (B : Type u) (ringB : CommRing B) (f : A →+* B),
      f.IndZariski ∧ WLocalSpace (PrimeSpectrum B) ∧
        closedPoints (PrimeSpectrum B) = PrimeSpectrum.zeroLocus (I.map f : Set B) ∧
        Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
