/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Coordinate ideals of projective closed subschemes

The affine chart ideals of a closed subscheme determine an intrinsic ideal in the
homogeneous coordinate ring by contraction from the ordinary coordinate localizations.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

variable {R : Type u} [CommRing R]

/-- The homogeneous coordinate ideal reconstructed from the affine chart ideals of a
closed subscheme of standard projective space. -/
def coordinateIdeal (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  ⨅ i : Fin (n + 1),
    Ideal.comap (algebraMap (MvPolynomial (Fin (n + 1)) R)
      (ProjectiveSpace.coordinateLocalizationAway (R := R) n i))
      (Ideal.map (ProjectiveSpace.coordinateAwayToLocalization (R := R) n i)
        (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) n i).hom.hom
          (Z.ideal (ProjectiveSpace.coordinateBasicOpen (R := R) n i))))

/-- A polynomial belongs to the coordinate ideal exactly when its image in every ordinary
coordinate localization belongs to the extended ideal of the corresponding affine chart. -/
theorem mem_coordinateIdeal_iff (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (f : MvPolynomial (Fin (n + 1)) R) :
    f ∈ coordinateIdeal n Z ↔
      ∀ i : Fin (n + 1),
        algebraMap (MvPolynomial (Fin (n + 1)) R)
            (ProjectiveSpace.coordinateLocalizationAway (R := R) n i) f ∈
          Ideal.map (ProjectiveSpace.coordinateAwayToLocalization (R := R) n i)
            (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) n i).hom.hom
              (Z.ideal (ProjectiveSpace.coordinateBasicOpen (R := R) n i))) := by
  simp only [coordinateIdeal, Submodule.mem_iInf, Ideal.mem_comap]

/-- The intrinsic coordinate ideal is homogeneous for the standard polynomial grading. -/
theorem coordinateIdeal_isHomogeneous (n : ℕ)
    (Z : (ProjectiveSpace.scheme R n).IdealSheafData) :
    (coordinateIdeal n Z).IsHomogeneous (ProjectiveSpace.grading R n) := sorry

/-- Extending the reconstructed coordinate ideal to an ordinary coordinate localization
recovers the extended ideal of the corresponding affine chart. -/
theorem map_coordinateIdeal (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (i : Fin (n + 1)) :
    Ideal.map (algebraMap (MvPolynomial (Fin (n + 1)) R)
        (ProjectiveSpace.coordinateLocalizationAway (R := R) n i))
        (coordinateIdeal n Z) =
      Ideal.map (ProjectiveSpace.coordinateAwayToLocalization (R := R) n i)
        (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) n i).hom.hom
          (Z.ideal (ProjectiveSpace.coordinateBasicOpen (R := R) n i))) := sorry

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
