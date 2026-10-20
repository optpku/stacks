module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Completion

@[expose] public section

open AlgebraicGeometry IsLocalRing
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- The affine-spectrum morphism induced by completion at the maximal ideal. -/
#check (AlgebraicGeometry.PuncturedSpectrum.completionSpecMap :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A],
      Spec (CommRingCat.of (AdicCompletion (maximalIdeal A) A)) ⟶
        Spec (CommRingCat.of A))

/- The affine completion morphism pulls the punctured open back to the punctured open. -/
#check (AlgebraicGeometry.PuncturedSpectrum.completionSpecMap_preimage_puncturedOpen :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      completionSpecMap A ⁻¹ᵁ puncturedOpen A =
        puncturedOpen (AdicCompletion (maximalIdeal A) A))

/- The morphism between punctured spectra induced by completion at the maximal ideal. -/
#check (AlgebraicGeometry.PuncturedSpectrum.completionMap :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      scheme (AdicCompletion (maximalIdeal A) A) ⟶ scheme A)

/- The punctured-spectrum completion morphism agrees with the affine completion morphism
after both open immersions. -/
#check (AlgebraicGeometry.PuncturedSpectrum.completionMap_comp_ι :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      completionMap A ≫ (puncturedOpen A).ι =
        (puncturedOpen (AdicCompletion (maximalIdeal A) A)).ι ≫
          completionSpecMap A)

end AlgebraicGeometry.PuncturedSpectrum
