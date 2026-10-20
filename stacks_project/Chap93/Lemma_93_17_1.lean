module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.GenericFiber

@[expose]
public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 93.17.1: For a proper flat family over `Spec (PowerSeries k)` with a Cohen–Macaulay,
equidimensional special fibre of dimension `d`, containment of `PowerSeries.X ^ (n - 1)` in the
`d`th Fitting ideal of the `n`th infinitesimal fibre implies smoothness of the generic fibre. -/
@[stacks 0E7T] #check (AlgebraicGeometry.Scheme.Hom.smooth_genericFiber_of_fittingIdealSheaf_contains_X_pow : ∀ {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (PowerSeries k))) [IsProper f] [Flat f] (d : ℕ) (h_cohenMacaulay : Scheme.CohenMacaulay (f.fiber (IsLocalRing.closedPoint (PowerSeries k)))) (h_equidimensional : EquidimensionalSpace (f.fiber (IsLocalRing.closedPoint (PowerSeries k)))) (h_dim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint (PowerSeries k))) = d) (n : ℕ+) (h_fitting : AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_contains_X_pow f n d), Smooth (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of (PowerSeries k))))))
