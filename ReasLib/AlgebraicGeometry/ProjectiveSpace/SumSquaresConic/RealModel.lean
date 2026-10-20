/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.LaurentSeries
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.SumSquaresConic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.SplitConic
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.GenusZero
public import ReasLib.AlgebraicGeometry.Scheme.Model.GoodReduction

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.SumSquaresConic

/-- Over complex power series, the sum of two squares factors into two linear terms. -/
theorem complexFactorization :
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) (PowerSeries ℂ)) ^ 2 +
        MvPolynomial.X 2 ^ 2 =
      (MvPolynomial.X 1 + MvPolynomial.C (PowerSeries.C Complex.I) * MvPolynomial.X 2) *
        (MvPolynomial.X 1 - MvPolynomial.C (PowerSeries.C Complex.I) * MvPolynomial.X 2) := sorry

/-- After coefficientwise extension to complex power series, the real sum-of-squares conic
is isomorphic over the base to the split conic. -/
@[stacks 0CDL]
theorem complexBaseChange_iso_splitConic :
    Nonempty
      (Over.mk (pullback.snd (toSpec (PowerSeries ℝ) PowerSeries.X)
          (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) (PowerSeries ℂ))))) ≅
        Over.mk (SplitConic.toSpec (PowerSeries ℂ) PowerSeries.X)) := sorry

/-- The sum-of-squares conic over real power series is regular. -/
@[stacks 0CDL, instance]
instance realModel_regular : Scheme.Regular (model (PowerSeries ℝ) PowerSeries.X) := sorry

/-- The special fibre of the real sum-of-squares conic is irreducible. -/
@[stacks 0CDL, instance]
instance realSpecialFiber_irreducible :
    IrreducibleSpace (specialFiber (PowerSeries ℝ) PowerSeries.X) := sorry

/-- The special fibre of the real sum-of-squares conic has a singular point. -/
@[stacks 0CDL]
theorem realSpecialFiber_singular :
    (Sing(specialFiber (PowerSeries ℝ) PowerSeries.X)).Nonempty := sorry

/-- The sum-of-squares conic is a minimal model over real power series. -/
@[stacks 0CDL, instance]
instance realModel_isMinimal :
    IsMinimalModel (toSpec (PowerSeries ℝ) PowerSeries.X) := sorry

/-- The generic fibre of the real sum-of-squares conic. -/
abbrev realGenericFiber : SchemeOverField (LaurentSeries ℝ) :=
  genericFiber (PowerSeries ℝ) PowerSeries.X (LaurentSeries ℝ)

/-- The real generic fibre is a curve. -/
instance realGenericFiber_curve : Curve realGenericFiber := sorry

/-- The real generic fibre is smooth. -/
instance realGenericFiber_smooth : Smooth realGenericFiber.hom := sorry

/-- The real generic fibre is projective. -/
instance realGenericFiber_projective : Projective realGenericFiber.hom := sorry

/-- The real generic fibre is proper. -/
instance realGenericFiber_proper : IsProper realGenericFiber.hom :=
  Projective.isProper realGenericFiber_projective

/-- The global functions on the real generic fibre are exactly the ground field. -/
theorem realGenericFiber_globalSections :
    Function.Bijective (Scheme.Hom.globalSectionsMap realGenericFiber.hom) := sorry

/-- The real conic model is Noetherian. -/
instance realModel_noetherian : IsNoetherian (model (PowerSeries ℝ) PowerSeries.X) := sorry

/-- The concrete regular model marked by the identity on its generic fibre. -/
def realRegularModel :
    RegularModel (PowerSeries ℝ) (LaurentSeries ℝ) realGenericFiber :=
  RegularModel.ofData (model (PowerSeries ℝ) PowerSeries.X)
    (toSpec (PowerSeries ℝ) PowerSeries.X) realModel_noetherian
    (IsMinimalModel.flat (f := toSpec (PowerSeries ℝ) PowerSeries.X))
    (IsMinimalModel.finiteType (f := toSpec (PowerSeries ℝ) PowerSeries.X))
    (IsMinimalModel.proper (f := toSpec (PowerSeries ℝ) PowerSeries.X))
    realModel_regular (Iso.refl _)

/-- The structural morphism underlying `realRegularModel` is the concrete conic morphism. -/
theorem realRegularModel_base :
    realRegularModel.base = toSpec (PowerSeries ℝ) PowerSeries.X := rfl

/-- Every minimal regular model of the real generic conic is isomorphic to the
sum-of-squares model, compatibly with its generic-fibre marking. -/
@[stacks 0CDL]
theorem realRegularModel_unique
    (M : RegularModel (PowerSeries ℝ) (LaurentSeries ℝ) realGenericFiber)
    [IsMinimalModel M.base] :
    RegularModel.Isomorphic realRegularModel M := sorry

/-- The real generic sum-of-squares conic has genus zero. -/
@[stacks 0CDL]
theorem realGenericFiber_genus_zero :
    SchemeOverField.genus realGenericFiber (topologicalKrullDim_eq_one realGenericFiber)
      realGenericFiber_globalSections = 0 := sorry

/-- The real generic sum-of-squares conic is not isomorphic to the projective line
over real Laurent series. -/
@[stacks 0CDL]
theorem realGenericFiber_not_iso_projectiveLine :
    ¬ Nonempty (realGenericFiber ≅ ProjectiveSpace.schemeOver (LaurentSeries ℝ) 1) := sorry

/-- The real generic sum-of-squares conic has no good reduction over real power series. -/
theorem realGenericFiber_not_hasGoodReduction :
    ¬ Scheme.Hom.hasGoodReduction (PowerSeries ℝ) (LaurentSeries ℝ) realGenericFiber := sorry

end AlgebraicGeometry.SumSquaresConic
