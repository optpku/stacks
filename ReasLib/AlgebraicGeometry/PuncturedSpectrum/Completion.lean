/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.RingTheory.Depth
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Completion of punctured spectra

The maximal-ideal adic completion of a Noetherian local ring induces a morphism
between its punctured spectrum and the punctured spectrum of the completion.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The affine-spectrum morphism induced by completion at the maximal ideal. -/
noncomputable def completionSpecMap :
    Spec (CommRingCat.of (AdicCompletion (maximalIdeal A) A)) ⟶
      Spec (CommRingCat.of A) :=
  Spec.map
    (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))

/-- The affine completion morphism pulls the punctured open back to the punctured open. -/
theorem completionSpecMap_preimage_puncturedOpen :
    completionSpecMap A ⁻¹ᵁ puncturedOpen A =
      puncturedOpen (AdicCompletion (maximalIdeal A) A) := sorry

/-- The morphism between punctured spectra induced by completion at the maximal ideal. -/
noncomputable def completionMap :
    scheme (AdicCompletion (maximalIdeal A) A) ⟶ scheme A :=
  (completionSpecMap A).resLE (puncturedOpen A)
    (puncturedOpen (AdicCompletion (maximalIdeal A) A))
    (le_of_eq (completionSpecMap_preimage_puncturedOpen A).symm)

/-- The punctured-spectrum completion morphism agrees with the affine completion morphism
after both open immersions. -/
theorem completionMap_comp_ι :
    completionMap A ≫ (puncturedOpen A).ι =
      (puncturedOpen (AdicCompletion (maximalIdeal A) A)).ι ≫
        completionSpecMap A := sorry

/-- For a Noetherian local ring of depth at least two, completion pullback is injective on
Picard groups of punctured spectra. -/
theorem completionMap_picardPullback_injective
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) :
    Function.Injective (Scheme.Hom.picardPullback (completionMap A)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
