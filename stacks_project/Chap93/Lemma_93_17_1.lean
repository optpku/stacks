module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.CrossRefAttribute
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

/-- Affine-open form of `fittingIdealSheaf_differentials_contains_X_pow`: the pulled-back
principal ideal of `PowerSeries.X ^ (n - 1)` is contained in the Fitting ideal on every affine
open of the infinitesimal fibre. -/
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

/-- Lemma 93.17.1: Let `k` be a field. Set `S = Spec (PowerSeries k)` and write `S_n` for
`Spec (k[t] ⧸ (t ^ n))`, identified with `Spec (PowerSeries k ⧸ m ^ n)`. Let `f : Y ⟶ S` be a
proper flat morphism of schemes whose special fibre `f.fiber (IsLocalRing.closedPoint (PowerSeries k))`
is Cohen–Macaulay and equidimensional of dimension `d`. Write `X_n` for the infinitesimal fibre
`InfinitesimalFiber.stage f n`. If for some `n : ℕ+` the `d`th Fitting ideal of
`Ω[(InfinitesimalFiber.toSpec f n).toShHom]` contains `PowerSeries.X ^ (n - 1)`, then the generic
fibre morphism `f.fiberToSpecResidueField (genericPoint S)` is smooth. -/
@[stacks 0E7T]
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
