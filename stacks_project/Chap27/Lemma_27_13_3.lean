/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
import StacksCheckRecall

@[expose] public section

/- Lemma 27.13.3: Projective `n`-space over `ℤ` is covered by the standard coordinate opens
`D₊(T_i)`, and each such open is isomorphic to affine `n`-space over `ℤ`. -/
@[stacks 01NG] #check
  (AlgebraicGeometry.ProjectiveSpace.iSup_coordinateBasicOpen_eq_top (R := ℤ) :
    ∀ n : ℕ,
      (⨆ i : Fin (n + 1),
        (AlgebraicGeometry.ProjectiveSpace.coordinateBasicOpen (R := ℤ) n i :
          (AlgebraicGeometry.ProjectiveSpace.scheme ℤ n).Opens)) = ⊤)

variable (n : ℕ) (i : Fin (n + 1))

#check
  (HomogeneousLocalization.homogeneousLocalizationCommRing :
    CommRing (AlgebraicGeometry.ProjectiveSpace.coordinateAway (R := ℤ) n i))

#check
  (AlgebraicGeometry.ProjectiveSpace.coordinate_mem_grading_one (R := ℤ) n i :
    AlgebraicGeometry.ProjectiveSpace.coordinate (R := ℤ) n i ∈
      AlgebraicGeometry.ProjectiveSpace.grading ℤ n 1)

#check
  (AlgebraicGeometry.ProjectiveSpace.dehomogenizeAt
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      MvPolynomial (Fin (n + 1)) ℤ →+* MvPolynomial (Fin n) ℤ)

#check
  (AlgebraicGeometry.ProjectiveSpace.dehomogenizeAt_coordinate_self
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      AlgebraicGeometry.ProjectiveSpace.dehomogenizeAt
          (R := ℤ) n i (Equiv.refl (Fin n))
          (AlgebraicGeometry.ProjectiveSpace.coordinate (R := ℤ) n i) = 1)

#check
  (AlgebraicGeometry.ProjectiveSpace.affineChartHom
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      MvPolynomial (Fin n) ℤ →+*
        AlgebraicGeometry.ProjectiveSpace.coordinateAway (R := ℤ) n i)

#check
  (AlgebraicGeometry.ProjectiveSpace.CoordinateChart.dehomogenization
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      AlgebraicGeometry.ProjectiveSpace.coordinateAway (R := ℤ) n i →+*
        MvPolynomial (Fin n) ℤ)

#check
  (AlgebraicGeometry.ProjectiveSpace.CoordinateChart.dehomogenization_comp_affineChartHom
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      (AlgebraicGeometry.ProjectiveSpace.CoordinateChart.dehomogenization
          (R := ℤ) n i (Equiv.refl (Fin n))).comp
          (AlgebraicGeometry.ProjectiveSpace.affineChartHom
            (R := ℤ) n i (Equiv.refl (Fin n))) =
        RingHom.id (MvPolynomial (Fin n) ℤ))

#check
  (AlgebraicGeometry.ProjectiveSpace.CoordinateChart.affineChartHom_comp_dehomogenization
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      (AlgebraicGeometry.ProjectiveSpace.affineChartHom
          (R := ℤ) n i (Equiv.refl (Fin n))).comp
          (AlgebraicGeometry.ProjectiveSpace.CoordinateChart.dehomogenization
            (R := ℤ) n i (Equiv.refl (Fin n))) =
        RingHom.id (AlgebraicGeometry.ProjectiveSpace.coordinateAway (R := ℤ) n i))

#check
  (AlgebraicGeometry.ProjectiveSpace.CoordinateChart.ringEquiv
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      AlgebraicGeometry.ProjectiveSpace.coordinateAway (R := ℤ) n i ≃+*
        MvPolynomial (Fin n) ℤ)

#check
  (AlgebraicGeometry.ProjectiveSpace.CoordinateChart.isoWith
    (R := ℤ) n i (Equiv.refl (Fin n)) :
      (AlgebraicGeometry.ProjectiveSpace.coordinateBasicOpen (R := ℤ) n i :
        (AlgebraicGeometry.ProjectiveSpace.scheme ℤ n).Opens).toScheme ≅
      AlgebraicGeometry.AffineSpace (Fin n)
        (AlgebraicGeometry.Spec (CommRingCat.of ℤ)))

variable (j : Fin n)

#check
  (AlgebraicGeometry.ProjectiveSpace.coordinateRatio
    (R := ℤ) n i (Equiv.refl (Fin n)) j :
      AlgebraicGeometry.ProjectiveSpace.coordinateAway (R := ℤ) n i)
