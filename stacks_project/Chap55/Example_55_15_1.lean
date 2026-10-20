module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.SumSquaresConic.RealModel
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Example 55.15.1: the conic T₁² + T₂² = πT₀² over real power series is the unique
minimal regular model of its generic fibre, with its given generic-fibre marking. -/
@[stacks 0CDL] #check
  (AlgebraicGeometry.SumSquaresConic.realRegularModel_unique :
    ∀ (M : RegularModel (PowerSeries ℝ) (LaurentSeries ℝ)
      AlgebraicGeometry.SumSquaresConic.realGenericFiber) [IsMinimalModel M.base],
      RegularModel.Isomorphic AlgebraicGeometry.SumSquaresConic.realRegularModel M)

#check (AlgebraicGeometry.SumSquaresConic.equation :
  ∀ (R : Type u) [CommRing R], R → MvPolynomial (Fin 3) R)

#check (AlgebraicGeometry.SumSquaresConic.equationIdeal_toIdeal :
  ∀ (R : Type u) [CommRing R] (π : R),
    (AlgebraicGeometry.SumSquaresConic.equationIdeal R π).toIdeal =
      Ideal.span ({AlgebraicGeometry.SumSquaresConic.equation R π} :
        Set (MvPolynomial (Fin 3) R)))

#check (AlgebraicGeometry.SumSquaresConic.toSpec :
  ∀ (R : Type u) [CommRing R] (π : R),
    AlgebraicGeometry.SumSquaresConic.model R π ⟶ Spec (CommRingCat.of R))

#check (AlgebraicGeometry.SumSquaresConic.specialFiber_def :
  ∀ (R : Type u) [CommRing R] (π : R) [IsLocalRing R],
    AlgebraicGeometry.SumSquaresConic.specialFiber R π =
      (AlgebraicGeometry.SumSquaresConic.toSpec R π).fiber (IsLocalRing.closedPoint R))

#check (AlgebraicGeometry.SumSquaresConic.genericFiber_def :
  ∀ (R : Type u) [CommRing R] (π : R) (K : Type u)
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K],
    AlgebraicGeometry.SumSquaresConic.genericFiber R π K =
      Over.mk (pullback.snd (AlgebraicGeometry.SumSquaresConic.toSpec R π)
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))))

#check (PowerSeries.map_X (algebraMap ℝ ℂ) :
  PowerSeries.map (algebraMap ℝ ℂ) PowerSeries.X = PowerSeries.X)

#check (AlgebraicGeometry.SumSquaresConic.complexFactorization :
  (MvPolynomial.X 1 : MvPolynomial (Fin 3) (PowerSeries ℂ)) ^ 2 +
      MvPolynomial.X 2 ^ 2 =
    (MvPolynomial.X 1 + MvPolynomial.C (PowerSeries.C Complex.I) * MvPolynomial.X 2) *
      (MvPolynomial.X 1 - MvPolynomial.C (PowerSeries.C Complex.I) * MvPolynomial.X 2))

#check (AlgebraicGeometry.SumSquaresConic.complexBaseChange_iso_splitConic :
  Nonempty
    (Over.mk (pullback.snd
        (AlgebraicGeometry.SumSquaresConic.toSpec (PowerSeries ℝ) PowerSeries.X)
        (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℝ) (PowerSeries ℂ))))) ≅
      Over.mk (AlgebraicGeometry.SplitConic.toSpec (PowerSeries ℂ) PowerSeries.X)))

#check (AlgebraicGeometry.SumSquaresConic.realModel_regular :
  Scheme.Regular (AlgebraicGeometry.SumSquaresConic.model (PowerSeries ℝ) PowerSeries.X))

#check (AlgebraicGeometry.SumSquaresConic.realSpecialFiber_irreducible :
  IrreducibleSpace
    (AlgebraicGeometry.SumSquaresConic.specialFiber (PowerSeries ℝ) PowerSeries.X))

#check (AlgebraicGeometry.SumSquaresConic.realSpecialFiber_singular :
  (Sing(AlgebraicGeometry.SumSquaresConic.specialFiber (PowerSeries ℝ) PowerSeries.X)).Nonempty)

#check (AlgebraicGeometry.SumSquaresConic.realModel_isMinimal :
  Scheme.Hom.IsMinimalModel
    (AlgebraicGeometry.SumSquaresConic.toSpec (PowerSeries ℝ) PowerSeries.X))

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber : SchemeOverField (LaurentSeries ℝ))

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_curve :
  Curve AlgebraicGeometry.SumSquaresConic.realGenericFiber)

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_smooth :
  Smooth AlgebraicGeometry.SumSquaresConic.realGenericFiber.hom)

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_projective :
  Projective AlgebraicGeometry.SumSquaresConic.realGenericFiber.hom)

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_proper :
  IsProper AlgebraicGeometry.SumSquaresConic.realGenericFiber.hom)

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_globalSections :
  Function.Bijective
    (Scheme.Hom.globalSectionsMap AlgebraicGeometry.SumSquaresConic.realGenericFiber.hom))

#check (AlgebraicGeometry.SumSquaresConic.realModel_noetherian :
  IsNoetherian (AlgebraicGeometry.SumSquaresConic.model (PowerSeries ℝ) PowerSeries.X))

#check (AlgebraicGeometry.SumSquaresConic.realRegularModel :
  RegularModel (PowerSeries ℝ) (LaurentSeries ℝ) AlgebraicGeometry.SumSquaresConic.realGenericFiber)

#check (AlgebraicGeometry.SumSquaresConic.realRegularModel_base :
  AlgebraicGeometry.SumSquaresConic.realRegularModel.base =
    AlgebraicGeometry.SumSquaresConic.toSpec (PowerSeries ℝ) PowerSeries.X)

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_genus_zero :
  SchemeOverField.genus AlgebraicGeometry.SumSquaresConic.realGenericFiber
    (topologicalKrullDim_eq_one AlgebraicGeometry.SumSquaresConic.realGenericFiber)
    AlgebraicGeometry.SumSquaresConic.realGenericFiber_globalSections = 0)

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_not_iso_projectiveLine :
  ¬ Nonempty (AlgebraicGeometry.SumSquaresConic.realGenericFiber ≅
    ProjectiveSpace.schemeOver (LaurentSeries ℝ) 1))

#check (AlgebraicGeometry.SumSquaresConic.realGenericFiber_not_hasGoodReduction :
  ¬ Scheme.Hom.hasGoodReduction (PowerSeries ℝ) (LaurentSeries ℝ)
    AlgebraicGeometry.SumSquaresConic.realGenericFiber)
