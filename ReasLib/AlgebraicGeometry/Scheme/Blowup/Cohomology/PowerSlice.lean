/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import ReasLib.Algebra.Module.IdealPower.Slice.Quotient
public import ReasLib.Algebra.Module.ProjectiveFactorIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.AssociatedGraded

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v

namespace AlgebraicGeometry.IsBlowup

/-- Under the associated-graded uniformity bounds, the transition of an `A`-linear map
from a finite ideal-projective `A ⧸ I ^ n`-module to `I ^ n / I ^ (2 * n)` is a finite
sum of maps to the lower fixed-width slice, multiplied by coefficients in `I ^ c`. -/
@[stacks 0GAC]
theorem powerSliceTransition_eq_sum_smul
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) (hcn : c ≤ n) (M : ModuleCat.{v} (A ⧸ I ^ n))
    [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)
    (φ : (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M →ₗ[A]
      Ideal.PowerSlice I A n n)
    (hn : max
      (associatedGradedUniformityThreshold I +
        (1 + associatedGradedFiberDimension I) * c)
      ((2 + associatedGradedFiberDimension I) * c) ≤ n)
    (hd : associatedGradedFiberDimension I = 0 →
      associatedGradedUniformityThreshold I + 2 * c ≤ n) :
    ∃ k : ℕ, ∃ a : Fin k → (I ^ c : Ideal A),
      ∃ ψ : Fin k →
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M →ₗ[A]
          Ideal.PowerSlice I A
            (n - (2 + associatedGradedFiberDimension I) * c) n,
        (Ideal.PowerSlice.transition I A n n
          (n - (1 + associatedGradedFiberDimension I) * c)
          (Nat.sub_le n ((1 + associatedGradedFiberDimension I) * c))).comp φ =
          ∑ i, (Ideal.PowerSlice.smulTo I A n
            (n - (2 + associatedGradedFiberDimension I) * c)
            (n - (1 + associatedGradedFiberDimension I) * c) c (a i)
            (Ideal.PowerSlice.coefficientIndex_le n c
              (associatedGradedFiberDimension I))).comp (ψ i) := sorry

/-- Under the associated-graded uniformity bounds, the degree-one Ext map from
`I ^ n / I ^ (2 * n)` to
`I ^ (n - (1 + d) * c) / I ^ (2 * (n - (1 + d) * c))`, where
`d = associatedGradedFiberDimension I`, vanishes for a derived `A ⧸ I ^ n`-module
concentrated in degrees `-1` and `0` with finite homology, provided the image of
`I ^ c` annihilates its degree-one Ext on every finite module. -/
theorem powerSliceExtOneMap_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) (hcn : c ≤ n)
    (hn : max
      (associatedGradedUniformityThreshold I +
        (1 + associatedGradedFiberDimension I) * c)
      ((2 + associatedGradedFiberDimension I) * c) ≤ n)
    (K : DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n)))
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    [Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I ^ n)) (-1)).obj K)]
    [Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I ^ n)) 0).obj K)]
    (hExt : twoTermExtOneAnnihilatedByIdealOnFiniteModules K
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c))) :
    (DerivedCategory.Ext.moduleFunctor K (1 : ℤ)).map
      (Ideal.PowerSlice.diagonalTransition I n
        (n - (1 + associatedGradedFiberDimension I) * c)
        (Nat.sub_le n ((1 + associatedGradedFiberDimension I) * c))) = 0 := sorry

end AlgebraicGeometry.IsBlowup
