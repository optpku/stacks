/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Spectrum.Prime.LocalizationSubalgebraImage
public import ReasLib.RingTheory.Spectrum.Prime.IncidenceImage
public import ReasLib.RingTheory.Spectrum.Prime.CuspParametrization
public import ReasLib.RingTheory.Spectrum.Prime.FermatCubicImage

@[expose] public section

open MvPolynomial PrimeSpectrum

universe u

/- Remark 111.24.5: finding the image as above is usually done by elimination theory.
This remark is not a new theorem and is not Chevalley. The preceding images are the
image of `D(f)` for `f = a0 + ⋯ + ar x^r` in `A[x]` (exercise-image, tag 0FKE) and
the four maps into `Spec(k[x, y])` (exercise-images, tag 02DZ).
Image of `Spec(k[x, yx⁻¹]) ⟶ Spec(k[x, y])`. -/
@[stacks 02E0]
#check (_root_.yxInvInclusion_comap_range :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Set.range (PrimeSpectrum.comap (YxInv.yxInvInclusion k).toRingHom) =
      (PrimeSpectrum.basicOpen (X 0 : MvPolynomial (Fin 2) k) :
          Set (PrimeSpectrum (MvPolynomial (Fin 2) k))) ∪
        PrimeSpectrum.zeroLocus ({X 0, X 1} : Set (MvPolynomial (Fin 2) k)))

-- Image of `Spec(k[x, y, a, b] / (ax - by - 1)) ⟶ Spec(k[x, y])`.
#check (_root_.axByHom_comap_range :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Set.range (PrimeSpectrum.comap (AxBy.axByHom k).toRingHom) =
      (PrimeSpectrum.basicOpen (X 0 : MvPolynomial (Fin 2) k) :
          Set (PrimeSpectrum (MvPolynomial (Fin 2) k))) ∪
        (PrimeSpectrum.basicOpen (X 1 : MvPolynomial (Fin 2) k) :
          Set (PrimeSpectrum (MvPolynomial (Fin 2) k))))

-- Image of the cusp map `Spec(k[t, 1 / (t - 1)]) ⟶ Spec(k[x, y])`.
#check (_root_.cuspHom_comap_range :
  ∀ (k : Type u) [Field k] [IsAlgClosed k],
    Set.range (PrimeSpectrum.comap (Cusp.cuspHom k).toRingHom) =
      PrimeSpectrum.zeroLocus ({X 1 ^ 2 - X 0 ^ 3} : Set (MvPolynomial (Fin 2) k)) \
        {pointToPoint (![1, 1] : Fin 2 → k)})

-- Image of the Fermat map `Spec(ℂ[s, t] / (s³ + t³ - 1)) ⟶ Spec(ℂ[x, y])`.
#check (_root_.fermatHom_comap_range :
  Set.range (PrimeSpectrum.comap FermatCubic.fermatHom.toRingHom) =
    PrimeSpectrum.zeroLocus
      ({FermatCubic.fermatImagePoly} : Set (MvPolynomial (Fin 2) ℂ)))
