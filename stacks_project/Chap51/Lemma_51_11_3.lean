/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Depth
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ENat

universe u v

/- Lemma 51.11.3 (1): for nested primes of an adic completion lying over nested primes of the
original ring, completion does not decrease the depth of the localized finite module. -/
@[stacks 0EHW]
#check (AdicCompletion.moduleDepth_atPrime_le :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      (I : Ideal A) [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
      (p q : PrimeSpectrum A) (p' q' : PrimeSpectrum (AdicCompletion I A))
      (h_pq : p.asIdeal ≤ q.asIdeal) (h_pq' : p'.asIdeal ≤ q'.asIdeal)
      (h_closed : I.map (algebraMap A (AdicCompletion I A)) ≤ q'.asIdeal)
      (h_p : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) p' = p)
      (h_q : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q' = q),
      moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M) ≤
        moduleDepth (Localization.AtPrime p'.asIdeal)
          (LocalizedModule.AtPrime p'.asIdeal (AdicCompletion I M)))

/- Lemma 51.11.3 (2): the depth at the smaller prime plus the dimension of the localized
quotient at the larger prime is unchanged by adic completion. -/
@[stacks 0EHW]
#check (AdicCompletion.moduleDepth_atPrime_add_quotientDim_eq :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      (I : Ideal A) [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (hdual : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex H)
      (p q : PrimeSpectrum A) (p' q' : PrimeSpectrum (AdicCompletion I A))
      (h_pq : p.asIdeal ≤ q.asIdeal) (h_pq' : p'.asIdeal ≤ q'.asIdeal)
      (h_closed : I.map (algebraMap A (AdicCompletion I A)) ≤ q'.asIdeal)
      (h_p : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) p' = p)
      (h_q : PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q' = q),
      (.some (moduleDepth (Localization.AtPrime p'.asIdeal)
          (LocalizedModule.AtPrime p'.asIdeal (AdicCompletion I M))) : WithBot ℕ∞) +
          ringKrullDim (p'.asIdeal.quotientAtPrime q') =
        (.some (moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞) +
          ringKrullDim (p.asIdeal.quotientAtPrime q))
