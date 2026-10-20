/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.FiniteExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Example 53.10.6: a nontrivial finite extension produces the explicit glued curve construction. -/
@[stacks 0DJC]
#check
  (AlgebraicGeometry.FiniteExtensionCurve.exists_gluedCurve :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k'],
      ¬ Function.Surjective (algebraMap k k') →
      ∃ e : CommRingCat.of (Localization.Away
          (AlgebraicGeometry.FiniteExtensionCurve.x k k')) ≅
        CommRingCat.of (Localization.Away
          (AlgebraicGeometry.FiniteExtensionCurve.y k')),
        ∃ h_e : e.hom.hom (IsLocalization.Away.invSelf
            (AlgebraicGeometry.FiniteExtensionCurve.x k k')) =
          algebraMap (Polynomial k') (Localization.Away
            (AlgebraicGeometry.FiniteExtensionCurve.y k'))
            (AlgebraicGeometry.FiniteExtensionCurve.y k'),
        ∃ X : SchemeOverField k,
          ∃ h_curve : Curve X,
          ∃ h_proper : IsProper X.hom,
          ∃ hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom),
          ∃ (a : Spec (CommRingCat.of
              (AlgebraicGeometry.FiniteExtensionCurve.coefficientRing k k')) ⟶ X.left)
            (b : Spec (CommRingCat.of (Polynomial k')) ⟶ X.left),
            ∃ h_a_base : AlgebraicGeometry.FiniteExtensionCurve.coefficientChartBase k k' =
              a ≫ X.hom,
            ∃ h_b_base : AlgebraicGeometry.FiniteExtensionCurve.polynomialChartBase k k' =
              b ≫ X.hom,
            ∃ h_a_open : IsOpenImmersion a,
            ∃ h_b_open : IsOpenImmersion b,
            ∃ h_pushout : IsPushout
              (AlgebraicGeometry.FiniteExtensionCurve.overlapToCoefficient k k')
              (AlgebraicGeometry.FiniteExtensionCurve.overlapToPolynomial k k' e) a b,
            ∃ (p : SchemeOverField.point k ⟶ X)
              (q : PrimeSpectrum
                (AlgebraicGeometry.FiniteExtensionCurve.coefficientRing k k')),
              ∃ h_qideal : q.asIdeal =
                AlgebraicGeometry.FiniteExtensionCurve.distinguishedIdeal k k',
              ∃ h_qpoint : a.base q =
                SchemeOverField.rationalPoint p (IsLocalRing.closedPoint k),
              ∃ h_singular : ¬ IsRegularLocalRing
                (SchemeOverField.stalkRing X
                  (SchemeOverField.rationalPoint p (IsLocalRing.closedPoint k))),
              ∃ h_maximal :
                (AlgebraicGeometry.FiniteExtensionCurve.distinguishedIdeal k k').IsMaximal,
              ∃ X' : SchemeOverField k',
                ∃ ν : X'.left ⟶ X.left,
                  ∃ e_projectiveLine : X' ≅ ProjectiveSpace.schemeOver k' 1,
                  ∃ h_finite : IsFinite ν,
                  ∃ h_birational : IsBirational ν,
                  ∃ h_regular : Scheme.Regular X'.left,
                    X'.hom ≫ FieldExtension.specMap k k' = ν ≫ X.hom)
