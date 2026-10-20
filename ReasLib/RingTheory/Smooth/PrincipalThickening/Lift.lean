/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Smooth
public import ReasLib.Algebra.Module.Torsion.Stability
public import ReasLib.RingTheory.Algebra.Quotient.PrincipalPower
public import ReasLib.RingTheory.Smooth.AtPrime.Map

/-!
# Lifting a smooth locus from a principal square thickening

This is the reusable principal-thickening form of Elkik's lifting step.  The
diagram is expressed through the canonical `PrincipalQuotient` maps, and the
localization condition is map-first, so no localized algebra instance is
required from callers.
-/

@[expose] public section

universe u v w x

open PrimeSpectrum
open scoped PrincipalIdeal

namespace Algebra.PrincipalThickening

variable {R : Type u} {Λ : Type v} {Cbar : Type w}
variable [CommRing R] [CommRing Λ] [CommRing Cbar] [Algebra R Λ]

/-- A reusable witness for lifting a map from a principal square thickening.
It owns the finitely presented intermediate algebra, the comparison maps, and
the smoothness conclusions needed by later approximation arguments. -/
@[stacks 07CP "principal thickening lift"]
structure Lift (π : R)
    [Algebra (R ⧸ principalPowerIdeal π 2) Cbar]
    (toTargetSquare :
      Cbar →ₐ[R ⧸ principalPowerIdeal π 2] PrincipalQuotient R Λ π 2) where
  /-- The lifted algebra over `R`. -/
  mid : Type x
  /-- The commutative-ring structure on the lifted algebra. -/
  instCommRing : CommRing mid
  /-- The `R`-algebra structure on the lifted algebra. -/
  instAlgebra : Algebra R mid
  /-- The lifted algebra is finitely presented over `R`. -/
  [finitePresentation : Algebra.FinitePresentation R mid]
  /-- The map from the lifted algebra to the target. -/
  toTarget : mid →ₐ[R] Λ
  /-- The first-order reduction of the source map. -/
  modFirst :
    Cbar →ₐ[R ⧸ principalPowerIdeal π 2] PrincipalQuotient R mid π 1
  /-- The lifted map agrees with the given map after reduction. -/
  factor :
    (PrincipalQuotient.Square.mapFirst toTarget π).comp modFirst =
      (PrincipalQuotient.Square.reduction (A := Λ) π).comp toTargetSquare
  /-- The lifted algebra is smooth away from `π`. -/
  smoothAway : (Localization.awayMap (algebraMap R mid) π).Smooth
  /-- Smooth points of the source lift to smooth points of the intermediate
  algebra. -/
  smoothAt (q : PrimeSpectrum (PrincipalQuotient R mid π 1)) :
    Algebra.SmoothAtPrime (R ⧸ principalPowerIdeal π 2) Cbar
        (comap modFirst.toRingHom q) →
      Algebra.SmoothAtPrime R mid
        (comap (Ideal.Quotient.mk
          (Ideal.map (algebraMap R mid) (principalPowerIdeal π 1))) q)
  /-- The descended map is smooth at every point lying over the original
  smooth locus. -/
  quotientSmoothAt (q : PrimeSpectrum (PrincipalQuotient R mid π 1)) :
    Algebra.SmoothAtPrime (R ⧸ principalPowerIdeal π 2) Cbar
        (comap modFirst.toRingHom q) →
      (PrincipalQuotient.FirstOrder.descend π modFirst).SmoothAtPrime q

attribute [instance] Lift.instCommRing Lift.instAlgebra Lift.finitePresentation

namespace Lift

variable {π : R} [Algebra (R ⧸ principalPowerIdeal π 2) Cbar]
variable {toTargetSquare :
  Cbar →ₐ[R ⧸ principalPowerIdeal π 2] PrincipalQuotient R Λ π 2}

/-- Build a principal-thickening lift from its intermediate algebra, comparison
maps, and smoothness properties. -/
@[stacks 07CP "principal thickening lift constructor"]
def of {B : Type x} [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (toTarget : B →ₐ[R] Λ)
    (modFirst :
      Cbar →ₐ[R ⧸ principalPowerIdeal π 2] PrincipalQuotient R B π 1)
    (factor :
      (PrincipalQuotient.Square.mapFirst toTarget π).comp modFirst =
        (PrincipalQuotient.Square.reduction (A := Λ) π).comp toTargetSquare)
    (smoothAway : (Localization.awayMap (algebraMap R B) π).Smooth)
    (smoothAt : ∀ q : PrimeSpectrum (PrincipalQuotient R B π 1),
      Algebra.SmoothAtPrime (R ⧸ principalPowerIdeal π 2) Cbar
          (comap modFirst.toRingHom q) →
        Algebra.SmoothAtPrime R B
          (comap (Ideal.Quotient.mk
            (Ideal.map (algebraMap R B) (principalPowerIdeal π 1))) q))
    (quotientSmoothAt : ∀ q : PrimeSpectrum (PrincipalQuotient R B π 1),
      Algebra.SmoothAtPrime (R ⧸ principalPowerIdeal π 2) Cbar
          (comap modFirst.toRingHom q) →
        (PrincipalQuotient.FirstOrder.descend π modFirst).SmoothAtPrime q) :
    Lift π toTargetSquare :=
  { mid := B
    instCommRing := inferInstance
    instAlgebra := inferInstance
    finitePresentation := inferInstance
    toTarget := toTarget
    modFirst := modFirst
    factor := factor
    smoothAway := smoothAway
    smoothAt := smoothAt
    quotientSmoothAt := quotientSmoothAt }

/-- The finite-presentation, comparison, and smoothness specification carried
by a principal-thickening lift. -/
@[stacks 07CP "principal thickening lift specification"]
theorem spec (L : Lift π toTargetSquare) :
    Algebra.FinitePresentation R L.mid ∧
      (PrincipalQuotient.Square.mapFirst L.toTarget π).comp L.modFirst =
        (PrincipalQuotient.Square.reduction (A := Λ) π).comp toTargetSquare ∧
      (Localization.awayMap (algebraMap R L.mid) π).Smooth ∧
      (∀ q : PrimeSpectrum (PrincipalQuotient R L.mid π 1),
        Algebra.SmoothAtPrime (R ⧸ principalPowerIdeal π 2) Cbar
            (comap L.modFirst.toRingHom q) →
          Algebra.SmoothAtPrime R L.mid
            (comap (Ideal.Quotient.mk
              (Ideal.map (algebraMap R L.mid) (principalPowerIdeal π 1))) q)) ∧
      ∀ q : PrimeSpectrum (PrincipalQuotient R L.mid π 1),
        Algebra.SmoothAtPrime (R ⧸ principalPowerIdeal π 2) Cbar
            (comap L.modFirst.toRingHom q) →
          (PrincipalQuotient.FirstOrder.descend π L.modFirst).SmoothAtPrime q := sorry

end Lift

/-- Lemma 16.6.1 (tag 07CP): a finitely presented algebra over `R / π²R` mapping to
`Λ / π²Λ` lifts to a finitely presented `R`-algebra with the prescribed smoothness away
from `π` and over the original smooth locus. -/
@[stacks 07CP]
theorem Lift.nonempty
    (π : R) [IsNoetherianRing R]
    [Algebra (R ⧸ principalPowerIdeal π 2) Cbar]
    [Algebra.FinitePresentation (R ⧸ principalPowerIdeal π 2) Cbar]
    (toTargetSquare :
      Cbar →ₐ[R ⧸ principalPowerIdeal π 2] Algebra.PrincipalQuotient R Λ π 2)
    (hAnnR : Module.IsTorsionStable R R π)
    (hAnnTarget : Module.IsTorsionStable Λ Λ (algebraMap R Λ π)) :
    Nonempty (Lift.{u, v, w, max u v w} π toTargetSquare) := sorry

end Algebra.PrincipalThickening
