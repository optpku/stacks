/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.RatSqrtNegOneAffineLine
import StacksCheckRecall

@[expose] public section

/- Exercise 111.33.16 (1): the affine line over `ℚ(i)` is an integral scheme. -/
@[stacks 0291] #check
  (AlgebraicGeometry.RatSqrtNegOneAffineLine.instIsIntegralScheme :
    AlgebraicGeometry.IsIntegral AlgebraicGeometry.RatSqrtNegOneAffineLine.scheme)

/- Exercise 111.33.16 (2): this scheme is 1-dimensional. -/
@[stacks 0291] #check
  (AlgebraicGeometry.RatSqrtNegOneAffineLine.topologicalKrullDim_eq_one :
    topologicalKrullDim AlgebraicGeometry.RatSqrtNegOneAffineLine.scheme = 1)

/- Exercise 111.33.16 (3): the structure morphism to `Spec ℚ` is of finite type. -/
@[stacks 0291] #check
  (AlgebraicGeometry.RatSqrtNegOneAffineLine.instFiniteTypeToSpecRat :
    AlgebraicGeometry.Scheme.Hom.FiniteType
      AlgebraicGeometry.RatSqrtNegOneAffineLine.toSpecRat)

/- Exercise 111.33.16 (4): the fiber product `Spec ℂ ×_Spec ℚ V` is not integral. -/
@[stacks 0291] #check
  (AlgebraicGeometry.RatSqrtNegOneAffineLine.not_isIntegral_complexBaseChange :
    ¬ AlgebraicGeometry.IsIntegral
      AlgebraicGeometry.RatSqrtNegOneAffineLine.complexBaseChange)
