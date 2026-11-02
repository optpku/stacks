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
     naturality := by
       intro W Z f
       exact ((Scheme.restrictFunctorΓ (X := U.left.left)).inv ≫
         Functor.whiskerLeft (chartOpens U).op
           (InducedCategory.Hom.hom A.obj.hom)).naturality f }⟩

/-- The concrete quasi-coherent scheme algebra obtained by restricting to a chart. -/
def onChart (A : X.QcAlgebraUnder) (U : smallEtaleSite X) : U.left.left.QcAlgebraUnder where
  obj := Under.mk (chartStructureMap A U)
  property := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Restrict a morphism of étale scheme charts to the inverse image of a target open. -/
def chartOpenRestrictionMap {U V : smallEtaleSite X} (m : U ⟶ V)
    (W : V.left.left.Opens) :
    (chartOpens U).obj (m.left.left ⁻¹ᵁ W) ⟶ (chartOpens V).obj W :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (m.left.left ∣_ W) (by
      change (m.left.left ∣_ W) ≫ (W.ι ≫ V.left.hom) =
        (m.left.left ⁻¹ᵁ W).ι ≫ U.left.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, m.left.w])) trivial (by
      let v : yoneda.obj V.left ⟶ X.functorOfPoints := V.hom
      let u : yoneda.obj U.left ⟶ X.functorOfPoints := U.hom
      have hw : yoneda.map m.left ≫ v = u := m.w
      change yoneda.map _ ≫ (yoneda.map _ ≫ v) = yoneda.map _ ≫ u
      rw [← Category.assoc, ← yoneda.map_comp]
      have h :
          (Over.homMk (m.left.left ∣_ W) (by
            change (m.left.left ∣_ W) ≫ (W.ι ≫ V.left.hom) =
              (m.left.left ⁻¹ᵁ W).ι ≫ U.left.hom
            rw [← Category.assoc, morphismRestrict_ι, Category.assoc, m.left.w]) :
            ((chartOpens U).obj (m.left.left ⁻¹ᵁ W)).left ⟶
              ((chartOpens V).obj W).left) ≫ Over.homMk W.ι rfl =
            Over.homMk (m.left.left ⁻¹ᵁ W).ι rfl ≫ m.left := by
        apply Over.OverMorphism.ext
        exact morphismRestrict_ι m.left.left W
      rw [h, yoneda.map_comp, Category.assoc, hw])

/-- The actual open-chart restriction commutes with inclusions of target opens. -/
theorem chartOpenRestrictionMap_naturality {U V : smallEtaleSite X} (m : U ⟶ V)
    {W Z : V.left.left.Opens} (f : W ⟶ Z) :
    chartOpenRestrictionMap m W ≫ (chartOpens V).map f =
      (chartOpens U).map (homOfLE (m.left.left.preimage_mono f.le)) ≫
        chartOpenRestrictionMap m Z := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Over.OverMorphism.ext
  exact morphismRestrict_homOfLE m.left.left W Z f.le

/-- The algebra map between two chart restrictions is the original sheaf restriction
on the actual open-chart morphism. -/
def onChartMap (A : X.QcAlgebraUnder) {U V : smallEtaleSite X} (m : U ⟶ V) :
    (onChart A V).obj ⟶ Scheme.qcAlgebraPushforwardTarget m.left.left (onChart A U) :=
  Under.homMk
    ⟨{ app := fun W ↦ A.obj.right.obj.map (chartOpenRestrictionMap m W.unop).op
       naturality := by
         intro W Z f
         exact (A.obj.right.obj.map_comp _ _).symm.trans
           ((congrArg A.obj.right.obj.map
             (congrArg Quiver.Hom.op (chartOpenRestrictionMap_naturality m f.unop))).trans
               (A.obj.right.obj.map_comp _ _)) }⟩ (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext W
      change ((Scheme.Opens.topIso W.unop).inv ≫ structureMap A ((chartOpens V).obj W.unop)) ≫
          A.obj.right.obj.map (chartOpenRestrictionMap m W.unop).op =
        m.left.left.app W.unop ≫
          ((Scheme.Opens.topIso (m.left.left ⁻¹ᵁ W.unop)).inv ≫
            structureMap A ((chartOpens U).obj (m.left.left ⁻¹ᵁ W.unop)))
      have h := (InducedCategory.Hom.hom A.obj.hom).naturality
        (chartOpenRestrictionMap m W.unop).op
      change (m.left.left ∣_ W.unop).appTop ≫
          structureMap A ((chartOpens U).obj (m.left.left ⁻¹ᵁ W.unop)) =
        structureMap A ((chartOpens V).obj W.unop) ≫
          A.obj.right.obj.map (chartOpenRestrictionMap m W.unop).op at h
      have htop : (Scheme.Opens.topIso W.unop).inv ≫ (m.left.left ∣_ W.unop).appTop =
          m.left.left.app W.unop ≫ (Scheme.Opens.topIso (m.left.left ⁻¹ᵁ W.unop)).inv := by
        change (Scheme.Opens.topIso W.unop).inv ≫ (m.left.left ∣_ W.unop).app ⊤ = _
        erw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_app_top,
          Scheme.Hom.appLE_eq_app, Iso.inv_hom_id_assoc]
      erw [Category.assoc, ← h, ← Category.assoc, htop, Category.assoc])

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
