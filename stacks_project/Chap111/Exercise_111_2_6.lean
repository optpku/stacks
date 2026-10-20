/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.IntegralClosure.FiniteColimit
public import ReasLib.RingTheory.Spectrum.Prime.Integral
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.2.6: if `A ⊂ B` is an integral ring extension, then the induced map
`Spec(B) → Spec(A)` is surjective, and `B` is the directed colimit of its finite-adjoin
subextensions. -/
@[stacks 078N]
#check (PrimeSpectrum.comap_surjective_of_integral :
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S],
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))

#check (@Algebra.FiniteAdjoin.instFinite :
  ∀ (R : Type u) (S : Type v) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S)
    (_ : Algebra.IsIntegral R S) (s : Finset S),
    Module.Finite R (Algebra.FiniteAdjoin.stage R S s))

#check (Algebra.FiniteAdjoin.toRing_bijective :
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S],
    Function.Bijective (Algebra.FiniteAdjoin.toRing R S))
