/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
The local ring and its strict henselization are represented in a common universe
because their spectrum morphism lives in `Scheme.{u}`. This is a representation
convention, not a mathematical size assumption.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable (Ash : Type u) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- The image of the punctured spectrum of a strict henselization lands in the
punctured spectrum of the original local ring. -/
theorem range_ι_specMap_subset_range_ι :
    Set.range
        (((puncturedOpen Ash).ι ≫
            Spec.map (CommRingCat.ofHom (algebraMap A Ash))).base) ⊆
      Set.range (puncturedOpen A).ι.base := sorry

/-- The morphism of punctured spectra induced by a strict henselization. -/
noncomputable def map_strictHenselization : scheme Ash ⟶ scheme A :=
  IsOpenImmersion.lift (puncturedOpen A).ι
    ((puncturedOpen Ash).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
    (range_ι_specMap_subset_range_ι Ash)

/-- Restriction of `map_strictHenselization` recovers the spectrum map of the
algebra map. -/
theorem map_strictHenselization_ι :
    map_strictHenselization Ash ≫ (puncturedOpen A).ι =
      (puncturedOpen Ash).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ash)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
