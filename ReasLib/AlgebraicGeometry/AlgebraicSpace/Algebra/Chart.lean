/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.MapOver

/-!
# Restrict quasi-coherent algebras to étale scheme charts

The native open-chart functor retains the actual scheme charts. Evaluating the
given algebra on these charts provides a Zariski algebra with its original
section maps. A morphism of étale charts induces the actual restriction maps
over its underlying scheme morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The native open-chart construction, expressed in the presentation of the small étale site. -/
def chartOpens (U : smallEtaleSite X) : U.left.left.Opens ⥤ smallEtaleSite X :=
  SmallEtale.openChart ((SmallEtale.fromPresentation X).obj U) ⋙
    SmallEtale.toPresentation X

/-- Restriction to open subschemes of an étale chart satisfies Zariski descent. -/
theorem chartPresheaf_isSheaf (A : X.QcAlgebraUnder) (U : smallEtaleSite X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology U.left.left)
      ((chartOpens U).op ⋙ A.obj.right.obj) := sorry

/-- The Zariski algebra sheaf on a chart, with its original carriers and restriction maps. -/
def chartSheaf (A : X.QcAlgebraUnder) (U : smallEtaleSite X) :
    Sheaf (Opens.grothendieckTopology U.left.left) CommRingCat.{u} :=
  ⟨(chartOpens U).op ⋙ A.obj.right.obj, chartPresheaf_isSheaf A U⟩

/-- The given algebra structure map on an open chart, using the native open-section isomorphism. -/
def chartStructureMap (A : X.QcAlgebraUnder) (U : smallEtaleSite X) :
    U.left.left.sheaf ⟶ chartSheaf A U :=
  ⟨{ app := fun W ↦ (Scheme.Opens.topIso W.unop).inv ≫
        structureMap A ((chartOpens U).obj W.unop)
     naturality := sorry }⟩

/-- The concrete quasi-coherent scheme algebra obtained by restricting to a chart. -/
def onChart (A : X.QcAlgebraUnder) (U : smallEtaleSite X) : U.left.left.QcAlgebraUnder where
  obj := Under.mk (chartStructureMap A U)
  property := sorry

/-- Restrict a morphism of étale scheme charts to the inverse image of a target open. -/
def chartOpenRestrictionMap {U V : smallEtaleSite X} (m : U ⟶ V)
    (W : V.left.left.Opens) :
    (chartOpens U).obj (m.left.left ⁻¹ᵁ W) ⟶ (chartOpens V).obj W :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (m.left.left ∣_ W) sorry) trivial sorry

/-- The algebra map between two chart restrictions is the original sheaf restriction
on the actual open-chart morphism. -/
def onChartMap (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    (onChart A V).obj ⟶ Scheme.qcAlgebraPushforwardTarget m.left.left (onChart A U) :=
  Under.homMk
    ⟨{ app := fun W ↦ A.obj.right.obj.map (chartOpenRestrictionMap m W.unop).op
       naturality := sorry }⟩ sorry

/-- The restricted algebra's ring of sections is the original ring on the corresponding chart. -/
theorem onChart_sections (A : X.QcAlgebraUnder) (U : smallEtaleSite X)
    (W : U.left.left.Opens) :
    Scheme.qcAlgebraSectionRing (onChart A U) W = sectionRing A ((chartOpens U).obj W) := rfl

/-- The contravariant spectrum map associated to a morphism of the actual étale charts. -/
def chartSpectrumMap (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    (Scheme.relativeSpectrumOver (onChart A U)).scheme ⟶
      (Scheme.relativeSpectrumOver (onChart A V)).scheme :=
  Scheme.relativeSpectrumMapOver m.left.left (onChartMap A m)

/-- The chart-spectrum map lies over the original scheme-chart morphism. -/
theorem chartSpectrumMap_toBase (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    chartSpectrumMap A m ≫ (Scheme.relativeSpectrumOver (onChart A V)).π =
      (Scheme.relativeSpectrumOver (onChart A U)).π ≫ m.left.left :=
  Scheme.relativeSpectrumMapOver_toBase m.left.left (onChartMap A m)

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
