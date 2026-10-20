module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Picard
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 52.27.3 -/
@[stacks 0F2F] #check
  (AlgebraicGeometry.PuncturedSpectrum.picardRestriction_surjective_of_trivialLocalPicard :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
      (hf_regular : IsRegular f)
      [IsAdicComplete (Ideal.span {f}) A]
      [Module.Finite A
        ((localCohomology (IsLocalRing.maximalIdeal A) 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))]
      [Module.Finite A
        ((localCohomology (IsLocalRing.maximalIdeal A) 2).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))]
      (h_h3 : IsZero
        ((localCohomology (IsLocalRing.maximalIdeal A) 3).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A))))))
      (h_localPicard : ∀ p : MaximalSpectrum (Localization.Away f),
        Subsingleton
          (Scheme.PicardGroup
            (PuncturedSpectrum.scheme (Localization.AtPrime p.asIdeal)))),
      let quotientMap :=
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let punctured := PuncturedSpectrum.puncturedOpen A
      Function.Surjective (Scheme.Hom.picardPullback (quotientMap ∣_ punctured)))
