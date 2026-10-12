/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionTwo.Patching
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 42.6.1: prescribed finite extensions at the nonclosed points of the zero locus
of a nonzerodivisor in a two-dimensional Noetherian local ring arise as the corresponding
localizations of one finite injective local extension with the same residue field, whose
cokernel is annihilated by a power of that nonzerodivisor. -/
@[stacks 0EAV]
#check
  (IsLocalRing.existsFiniteExtensionWithLocalizations :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (hdim : ringKrullDim A = 2) (t : A)
      (htm : t ∈ IsLocalRing.maximalIdeal A) (ht : t ∈ nonZeroDivisors A)
      {r : ℕ} (q : Fin r → PrimeSpectrum A) (hq_injective : Function.Injective q)
      (hq_ne_closedPoint : ∀ i, q i ≠ IsLocalRing.closedPoint A)
      (hV : PrimeSpectrum.zeroLocus ({t} : Set A) =
        Set.insert (IsLocalRing.closedPoint A) (Set.range q))
      (Bq : Fin r → Type u) [∀ i, CommRing (Bq i)]
      [∀ i, Algebra (Localization.AtPrime (q i).asIdeal) (Bq i)]
      [∀ i, Module.Finite (Localization.AtPrime (q i).asIdeal) (Bq i)]
      (hinjective : ∀ i, Function.Injective
        (algebraMap (Localization.AtPrime (q i).asIdeal) (Bq i)))
      (hann : ∀ i, Module.IsAnnihilatedByPower
        (Ideal.span
          ({algebraMap A (Localization.AtPrime (q i).asIdeal) t} :
            Set (Localization.AtPrime (q i).asIdeal)))
        (Bq i ⧸
          (Algebra.linearMap (Localization.AtPrime (q i).asIdeal) (Bq i)).range)),
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
          (_ : IsLocalRing C) (_ : IsLocalHom (algebraMap A C))
          (_ : Module.Finite A C) (_ : Function.Injective (algebraMap A C))
          (_ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A C)))
          (e : ∀ i, Localization
            (Submonoid.map (algebraMap A C) (q i).asIdeal.primeCompl) ≃+* Bq i)
          (_ : ∀ i, (e i).toRingHom.comp
            (Localization.AtPrime.map (algebraMap A C) (q i).asIdeal) =
              algebraMap (Localization.AtPrime (q i).asIdeal) (Bq i)),
        Module.IsAnnihilatedByPower (Ideal.span ({t} : Set A))
          (C ⧸ (Algebra.linearMap A C).range))

end
