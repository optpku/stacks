module

public import ReasLib.AlgebraicGeometry.Curve.CubicQuartic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

/- Exercise 111.51.4 -/
@[stacks 02FJ] #check
  (AlgebraicGeometry.CubicQuartic.subset_firstOpen_sup_lastOpen :
    AlgebraicGeometry.CubicQuartic.ι ⁻¹ᵁ
      (AlgebraicGeometry.CubicQuartic.firstOpen ⊔ AlgebraicGeometry.CubicQuartic.lastOpen) = ⊤)

#check
  (AlgebraicGeometry.CubicQuartic.instCurve :
    Curve AlgebraicGeometry.CubicQuartic.schemeOver)

#check
  (AlgebraicGeometry.CubicQuartic.instSmooth :
    Smooth AlgebraicGeometry.CubicQuartic.schemeOver.hom)

#check
  (AlgebraicGeometry.CubicQuartic.instProjective :
    Projective AlgebraicGeometry.CubicQuartic.schemeOver.hom)

#check
  (AlgebraicGeometry.CubicQuartic.xProjection_degree_eq_three :
    AlgebraicGeometry.CubicQuartic.xProjection.inducedFunctionFieldDegree = 3)

#check
  (AlgebraicGeometry.CubicQuartic.ramificationIndexAt_xProjection :
    ∀ (x : closedPoints AlgebraicGeometry.CubicQuartic.scheme) {n : ℕ},
      AlgebraicGeometry.CubicQuartic.xProjection.ramificationIndexAt x.1 = n ↔
        n = 3 ∧ (∃ a : ℂ, a ^ 8 = 1 ∧
            AlgebraicGeometry.CubicQuartic.xProjection.base x.1 =
              (AlgebraicGeometry.CubicQuartic.xChartPoint a).base
                (IsLocalRing.closedPoint ℂ)) ∨
        n = 1 ∧ (∀ a : ℂ, a ^ 8 = 1 →
            AlgebraicGeometry.CubicQuartic.xProjection.base x.1 ≠
              (AlgebraicGeometry.CubicQuartic.xChartPoint a).base
                (IsLocalRing.closedPoint ℂ)))

#check
  (AlgebraicGeometry.CubicQuartic.genus_eq_six :
    Curve.genus AlgebraicGeometry.CubicQuartic.schemeOver = 6)

#check
  (AlgebraicGeometry.CubicQuartic.xProjection_comp_toImage :
    AlgebraicGeometry.CubicQuartic.generatingMap.toImage ≫
        AlgebraicGeometry.CubicQuartic.xProjection =
      AlgebraicGeometry.CubicQuartic.affineClosedToPlane ≫
        AlgebraicGeometry.CubicQuartic.planeToChartX 0)

#check
  (AlgebraicGeometry.CubicQuartic.ramificationIndexAt_first :
    ∀ (a : ℂ) (ha : a ^ 4 = 1),
      AlgebraicGeometry.CubicQuartic.xProjection.ramificationIndexAt
          ((AlgebraicGeometry.CubicQuartic.firstRamificationPoint a ha).base
            (IsLocalRing.closedPoint ℂ)) = 3)

#check
  (AlgebraicGeometry.CubicQuartic.ramificationIndexAt_last :
    ∀ (a : ℂ) (ha : a ^ 4 = -1),
      AlgebraicGeometry.CubicQuartic.xProjection.ramificationIndexAt
          ((AlgebraicGeometry.CubicQuartic.lastRamificationPoint a ha).base
            (IsLocalRing.closedPoint ℂ)) = 3)
