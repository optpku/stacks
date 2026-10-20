module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Picard.Torsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open scoped ENat

universe u

/- Lemma 52.26.1: Let A be a Noetherian local ring and f a nonzerodivisor in its
maximal ideal. Assume depth(A/fA) ≥ 2, equivalently depth(A) ≥ 3. Pullback from
the Picard group of the punctured spectrum of A to that of A/fA is injective
on torsion. -/
@[stacks 0F2A] #check
  (AlgebraicGeometry.PuncturedSpectrum.picardPullback_injective_on_torsion :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
      (hf_regular : IsRegular f) (hdepth : (3 : ℕ∞) ≤ moduleDepth A A),
      let quotientMap :=
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let punctured := PuncturedSpectrum.puncturedOpen A
      Set.InjOn (Scheme.Hom.picardPullback (quotientMap ∣_ punctured))
        (AddCommGroup.torsion (Scheme.PicardGroup punctured.toScheme)))
