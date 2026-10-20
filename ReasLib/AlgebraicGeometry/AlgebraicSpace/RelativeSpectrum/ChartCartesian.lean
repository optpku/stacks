/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.GluedChartEvaluation
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.PointMap

/-!
# Actual cartesian lifts of the chart spectra

Section evaluation gives the algebra point on a test scheme in the chart
pullback square. The explicit scheme point map supplies the mediating morphism,
so the limiting cone contains an actual lift operation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Scheme.{u}}

/-- Restrict an actual cartesian test cone to an open of its source scheme chart. -/
theorem relativeSpectrumChartPoint_restrictedTriangle (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left)
    (Q : R.left.left.Opens) :
    ((f ⁻¹ᵁ Q).ι ≫ e) ≫ (Scheme.relativeSpectrumOver (onChart A V)).π =
      (f ∣_ Q) ≫ ((relativeSpectrumOpenChartInclusion R Q) ≫ m).left.left := sorry

/-- The actual algebra map on the test scheme's inverse-image opens, given by section evaluation. -/
def relativeSpectrumChartPointAlgebra (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left) :
    (onChart A R).obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap f.toShHom) :=
  Under.homMk
    ⟨{ app := fun Q ↦
        relativeSpectrumGluedPointEvaluation A
          ((relativeSpectrumOpenChartInclusion R Q.unop) ≫ m)
          (f ∣_ Q.unop) ((f ⁻¹ᵁ Q.unop).ι ≫ e)
          (relativeSpectrumChartPoint_restrictedTriangle A m f e h Q.unop) ≫
        (Scheme.Opens.topIso (f ⁻¹ᵁ Q.unop)).hom
       naturality := sorry }⟩ sorry

/-- The mediating scheme morphism is the actual point-to-morphism construction. -/
def relativeSpectrumChartPullbackLift (A : X.QcAlgebraUnder)
    {R V : smallEtaleSite X} (m : R ⟶ V) (f : E ⟶ R.left.left)
    (e : E ⟶ (Scheme.relativeSpectrumOver (onChart A V)).scheme)
    (h : e ≫ (Scheme.relativeSpectrumOver (onChart A V)).π = f ≫ m.left.left) :
    E ⟶ (Scheme.relativeSpectrumOver (onChart A R)).scheme :=
  Scheme.relativeSpectrumPointMap (onChart A R)
    ⟨f, relativeSpectrumChartPointAlgebra A m f e h⟩

/-- The cartesian chart cone has the actual spectrum map and structural scheme map as projections. -/
def relativeSpectrumChartPullbackCone (A : X.QcAlgebraUnder) {R V : smallEtaleSite X}
    (m : R ⟶ V) :
    PullbackCone (Scheme.relativeSpectrumOver (onChart A V)).π m.left.left :=
  PullbackCone.mk (chartSpectrumMap A m) (Scheme.relativeSpectrumOver (onChart A R)).π
    (chartSpectrumMap_toBase A m)

/-- The chart cone is limiting with its explicitly constructed point-based lift operation. -/
def relativeSpectrumChartPullbackIsLimit (A : X.QcAlgebraUnder) {R V : smallEtaleSite X}
    (m : R ⟶ V) : IsLimit (relativeSpectrumChartPullbackCone A m) :=
  PullbackCone.IsLimit.mk (chartSpectrumMap_toBase A m)
    (fun c ↦ relativeSpectrumChartPullbackLift A m c.snd c.fst c.condition)
    sorry sorry sorry

/-- The actual spectrum map square is cartesian over every morphism of étale scheme charts. -/
theorem chartSpectrumMap_isPullback (A : X.QcAlgebraUnder) {R V : smallEtaleSite X} (m : R ⟶ V) :
    IsPullback (chartSpectrumMap A m) (Scheme.relativeSpectrumOver (onChart A R)).π
      (Scheme.relativeSpectrumOver (onChart A V)).π m.left.left :=
  IsPullback.of_isLimit (relativeSpectrumChartPullbackIsLimit A m)

end AlgebraicGeometry.AlgebraicSpace
