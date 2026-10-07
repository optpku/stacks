module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Picard
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 52.27.1 -/
@[stacks 0F2D] #check
  (AlgebraicGeometry.PuncturedSpectrum.picardNeighborhoodRestriction_surjective :
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
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))),
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A
    let closedFiber := (quotientMap ⁻¹ᵁ punctured).toScheme
    ∀ x : Scheme.PicardGroup closedFiber,
      ∃ (V : punctured.toScheme.Opens)
        (j : closedFiber ⟶ V.toScheme),
        j ≫ V.ι = quotientMap ∣_ punctured ∧
          ∃ y : Scheme.PicardGroup V.toScheme,
            Scheme.Hom.picardPullback j y = x)
