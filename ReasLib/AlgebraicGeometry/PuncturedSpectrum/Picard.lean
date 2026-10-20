module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- A Picard class on the punctured spectrum of a principal closed fiber extends to a
Picard class on an open neighborhood in the ambient punctured spectrum. -/
theorem picardNeighborhoodRestriction_surjective
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
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
          (A ⧸ (Ideal.span {f} • (⊤ : Submodule A A)))))) :
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := puncturedOpen A
    let closedFiber := (quotientMap ⁻¹ᵁ punctured).toScheme
    ∀ x : Scheme.PicardGroup closedFiber,
      ∃ (V : punctured.toScheme.Opens)
        (j : closedFiber ⟶ V.toScheme),
        j ≫ V.ι = quotientMap ∣_ punctured ∧
          ∃ y : Scheme.PicardGroup V.toScheme,
            Scheme.Hom.picardPullback j y = x := sorry

/-- Under the local Picard triviality hypothesis after inverting `f`, every Picard
class on the punctured closed fiber extends to the punctured spectrum. -/
theorem picardRestriction_surjective_of_trivialLocalPicard
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
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
          (PuncturedSpectrum.scheme (Localization.AtPrime p.asIdeal)))) :
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := puncturedOpen A
    Function.Surjective (Scheme.Hom.picardPullback (quotientMap ∣_ punctured)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
