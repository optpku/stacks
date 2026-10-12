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

/- Lemma 38.25.11: Let `A` be a local ring and let `I, J ⊆ A` be ideals, with
`I ≠ ⊤`. If `J` is finitely generated and `I ≤ J ^ n` for every `n ≥ 1`, then
`V(I)` contains the closed points of `PrimeSpectrum A \ V(J)`. -/
@[stacks 0ATB] #check
  (@Ideal.zeroLocus_contains_closedPoints_compl :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A]
      (I J : Ideal A) (hI : I ≠ ⊤) (hJ : J.FG)
      (hIJ : ∀ n : ℕ, 1 ≤ n → I ≤ J ^ n),
      Subtype.val '' closedPoints
        ((PrimeSpectrum.zeroLocus (J : Set A))ᶜ : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus (I : Set A))
