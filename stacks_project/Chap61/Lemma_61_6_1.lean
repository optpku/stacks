/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.ConnectedComponents
import StacksCheckRecall

@[expose] public section

universe u

open PrimeSpectrum

/- Lemma 61.6.1: for a ring `A` and a closed subset `T` of
`ConnectedComponents (PrimeSpectrum A)`, there exists a surjective
ind-Zariski ring map `f : A →+* B` such that `PrimeSpectrum.comap f` is a
homeomorphism onto the inverse image `ConnectedComponents.mk ⁻¹' T` in
`PrimeSpectrum A`. Surjectivity of the ring homomorphism makes its `comap` a
closed embedding, hence a homeomorphism onto its image. -/
@[stacks 097C] #check
  (RingHom.IndZariski.exists_surjective_of_isClosed_connectedComponents :
    ∀ {A : Type u} [CommRing A] {T : Set (ConnectedComponents (PrimeSpectrum A))},
    IsClosed T →
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      Function.Surjective f ∧ f.IndZariski ∧
        Set.range (comap f) = ConnectedComponents.mk ⁻¹' T)

#check
  (RingHom.IndZariski.exists_quotientMk_of_isClosed_connectedComponents :
    ∀ {A : Type u} [CommRing A] {T : Set (ConnectedComponents (PrimeSpectrum A))},
    IsClosed T →
    ∃ I : Ideal A,
      (Ideal.Quotient.mk I).IndZariski ∧
        zeroLocus (I : Set A) = ConnectedComponents.mk ⁻¹' T)
