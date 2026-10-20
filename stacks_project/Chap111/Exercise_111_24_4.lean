/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.LocalizationSubalgebraImage
public import ReasLib.RingTheory.Spectrum.Prime.IncidenceImage
public import ReasLib.RingTheory.Spectrum.Prime.CuspParametrization
public import ReasLib.RingTheory.Spectrum.Prime.FermatCubicImage
import StacksCheckRecall

@[expose] public section

noncomputable section

open MvPolynomial PrimeSpectrum

universe u

/- Exercise 111.24.4 (1) -/
@[stacks 02DZ]
#check (_root_.yxInvInclusion_comap_range :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Set.range (PrimeSpectrum.comap (YxInv.yxInvInclusion k).toRingHom) =
      (PrimeSpectrum.basicOpen (X 0 : MvPolynomial (Fin 2) k) :
          Set (PrimeSpectrum (MvPolynomial (Fin 2) k))) ∪
        PrimeSpectrum.zeroLocus ({X 0, X 1} : Set (MvPolynomial (Fin 2) k)))

/- Exercise 111.24.4 (2) -/
@[stacks 02DZ]
#check (_root_.axByHom_comap_range :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Set.range (PrimeSpectrum.comap (AxBy.axByHom k).toRingHom) =
      (PrimeSpectrum.basicOpen (X 0 : MvPolynomial (Fin 2) k) :
          Set (PrimeSpectrum (MvPolynomial (Fin 2) k))) ∪
        (PrimeSpectrum.basicOpen (X 1 : MvPolynomial (Fin 2) k) :
          Set (PrimeSpectrum (MvPolynomial (Fin 2) k))))

/- Exercise 111.24.4 (3) -/
@[stacks 02DZ]
#check (_root_.cuspHom_comap_range :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Set.range (PrimeSpectrum.comap (Cusp.cuspHom k).toRingHom) =
      PrimeSpectrum.zeroLocus ({X 1 ^ 2 - X 0 ^ 3} : Set (MvPolynomial (Fin 2) k)) \
        {pointToPoint (![1, 1] : Fin 2 → k)})

/- Exercise 111.24.4 (4) -/
@[stacks 02DZ]
#check (_root_.fermatHom_comap_range :
  Set.range (PrimeSpectrum.comap FermatCubic.fermatHom.toRingHom) =
    PrimeSpectrum.zeroLocus
      ({FermatCubic.fermatImagePoly} : Set (MvPolynomial (Fin 2) ℂ)))
