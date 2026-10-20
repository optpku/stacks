/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.PowerSeries.Inverse
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.InfinitesimalFiber
public import ReasLib.Topology.KrullDimension.Equidimensional

/-!
# A Fitting criterion for smoothness of the generic fibre
-/

@[expose]
public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The `d`th Fitting ideal of relative differentials on the `n`th infinitesimal fibre contains
the image of `PowerSeries.X ^ (n - 1)`. -/
def fittingIdealSheaf_differentials_contains_X_pow {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of (PowerSeries k))) (n : ℕ+) (d : ℕ) : Prop :=
  (idealSheafDataOfIdealOnSpec
      (Ideal.span
        {Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (PowerSeries k)) ^ (n : ℕ))
          (PowerSeries.X ^ ((n : ℕ) - 1))})).comap
      (InfinitesimalFiber.toSpec f n) ≤
    Scheme.fittingIdealSheaf (Ω[(InfinitesimalFiber.toSpec f n).toShHom]) d

/-- The containment of the principal power-series ideal in the Fitting ideal on the
infinitesimal fibre can be checked on every affine open. -/
theorem fittingIdealSheaf_differentials_contains_X_pow_iff {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (PowerSeries k))) (n : ℕ+) (d : ℕ) :
    fittingIdealSheaf_differentials_contains_X_pow f n d ↔
      ∀ U : (InfinitesimalFiber.stage f n).affineOpens,
        ((idealSheafDataOfIdealOnSpec
            (Ideal.span
              {Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (PowerSeries k)) ^ (n : ℕ))
                (PowerSeries.X ^ ((n : ℕ) - 1))})).comap
          (InfinitesimalFiber.toSpec f n)).ideal U ≤
          (Scheme.fittingIdealSheaf (Ω[(InfinitesimalFiber.toSpec f n).toShHom]) d).ideal U :=
  sorry

/-- A proper flat family over `Spec (PowerSeries k)` with a Cohen–Macaulay, equidimensional
special fibre of dimension `d` has smooth generic fibre when the `d`th Fitting ideal of relative
differentials on an infinitesimal fibre contains the image of `PowerSeries.X ^ (n - 1)`. -/
theorem smooth_genericFiber_of_fittingIdealSheaf_contains_X_pow {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (PowerSeries k))) [IsProper f] [Flat f]
    (d : ℕ)
    (h_cohenMacaulay :
      Scheme.CohenMacaulay (f.fiber (IsLocalRing.closedPoint (PowerSeries k))))
    (h_equidimensional :
      EquidimensionalSpace (f.fiber (IsLocalRing.closedPoint (PowerSeries k))))
    (h_dim :
      topologicalKrullDim (f.fiber (IsLocalRing.closedPoint (PowerSeries k))) = d)
    (n : ℕ+) (h_fitting : fittingIdealSheaf_differentials_contains_X_pow f n d) :
    Smooth (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of (PowerSeries k))))) :=
  sorry

end AlgebraicGeometry.Scheme.Hom
