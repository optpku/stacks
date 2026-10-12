/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.ZeroLocusCover
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 38.25.10: let `A` be a local domain that is not a field and let `S` be a set
of finitely generated ideals closed under products. If the union of the zero loci of the
ideals in `S` is the complement of the generic point of `PrimeSpectrum A`, then the
intersection of the ideals in `S` is zero. -/
@[stacks 0ATA] #check (@Ideal.sInf_eq_bot_of_zeroLocus_cover :
  ∀ {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A],
    (¬ IsField A) → (S : Set (Ideal A)) →
    (∀ I ∈ S, I.FG) →
    (∀ I ∈ S, ∀ J ∈ S, I * J ∈ S) →
      (⋃ I ∈ S, PrimeSpectrum.zeroLocus (I : Set A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A))ᶜ →
    sInf S = ⊥)
