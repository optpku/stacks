/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Three-member fpqc families on the affine plane

The two coordinate basic opens become fpqc covering families after adjoining
either the formal power-series spectrum or the spectrum of the origin stalk.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped PrimeSpectrum

universe u

namespace AlgebraicGeometry.Scheme.Fpqc.AffinePlaneFamily

/-- The three-member affine-plane family consisting of the two coordinate
basic opens and the formal power-series spectrum. -/
noncomputable def powerSeries (k : Type u) [Field k] :
    Fin 3 → Over (PuncturedAffineSpace.coordinateSpectrum (Fin 2) k) :=
  fun i ↦
    Fin.cases
      (Over.mk (Scheme.Opens.ι
        (D(PuncturedAffineSpace.coordinate (Fin 2) k (0 : Fin 2)))))
      (Fin.cases
        (Over.mk (Scheme.Opens.ι
          (D(PuncturedAffineSpace.coordinate (Fin 2) k (1 : Fin 2)))))
        (fun _ ↦
          Over.mk (Spec.map
            (CommRingCat.ofHom MvPolynomial.coeToMvPowerSeries.ringHom))))
      i

/-- The three-member affine-plane family consisting of the two coordinate
basic opens and the spectrum of the local ring at the origin. -/
noncomputable def stalk (k : Type u) [Field k] :
    Fin 3 → Over (PuncturedAffineSpace.coordinateSpectrum (Fin 2) k) :=
  fun i ↦
    Fin.cases
      (Over.mk (Scheme.Opens.ι
        (D(PuncturedAffineSpace.coordinate (Fin 2) k (0 : Fin 2)))))
      (Fin.cases
        (Over.mk (Scheme.Opens.ι
          (D(PuncturedAffineSpace.coordinate (Fin 2) k (1 : Fin 2)))))
        (fun _ ↦
          Over.mk (Scheme.fromSpecStalk
            (PuncturedAffineSpace.coordinateSpectrum (Fin 2) k)
            (PuncturedAffineSpace.coordinateOrigin (Fin 2) k))))
      i

/-- The coordinate basic opens together with the formal power-series spectrum
form an fpqc covering family of the affine plane. -/
theorem powerSeries_fpqcCovering (k : Type u) [Field k] :
    Scheme.FpqcCovering (powerSeries k) := sorry

/-- The coordinate basic opens together with the origin stalk spectrum form
an fpqc covering family of the affine plane. -/
theorem stalk_fpqcCovering (k : Type u) [Field k] :
    Scheme.FpqcCovering (stalk k) := sorry

end AlgebraicGeometry.Scheme.Fpqc.AffinePlaneFamily
