module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.ChartCartesian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.CommRingAdjunction

/-!
# The actual algebra point of the constructed affine spectrum atlas

For every étale test chart of X, pull back the stored base atlas using its
supplied relative representability data. Each comma chart over the spectrum
pullback gives an actual scheme map to this overlap and a map to the spectrum
atlas. Section evaluation yields its ring map; the canonical direct-image
cone lift assembles those maps into the atlas algebra point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The constructed atlas structural map, as the canonical morphism of algebraic spaces. -/
abbrev relativeSpectrumDescentAtlasHomToX (A : X.QcAlgebraUnder) :
    ofOver (relativeSpectrumDescentAtlas A) ⟶ X :=
  relativeSpectrumDescentAtlasToX A

/-- The actual represented overlap of the stored atlas with an arbitrary étale scheme chart. -/
def relativeSpectrumAtlasOverlapChart (X : AlgebraicSpace S) (W : smallEtaleSite X) :
    smallEtaleSite X :=
  @smallEtaleSite.mk S X ((atlasHom_presheaf_etale X).rep.pullback W.hom)
    ((atlasHom_presheaf_etale X).rep.fst W.hom ≫ atlasHom X) sorry

/-- The overlap's actual projection to the stored base atlas. -/
def relativeSpectrumAtlasOverlapToAtlas (X : AlgebraicSpace S) (W : smallEtaleSite X) :
    relativeSpectrumAtlasOverlapChart X W ⟶ relativeSpectrumAtlasChart X :=
  MorphismProperty.CostructuredArrow.homMk ((atlasHom_presheaf_etale X).rep.fst' W.hom)
    trivial sorry

/-- The overlap's actual projection to the test scheme chart. -/
def relativeSpectrumAtlasOverlapToChart (X : AlgebraicSpace S) (W : smallEtaleSite X) :
    relativeSpectrumAtlasOverlapChart X W ⟶ W :=
  MorphismProperty.CostructuredArrow.homMk ((atlasHom_presheaf_etale X).rep.snd W.hom)
    trivial ((atlasHom_presheaf_etale X).rep.w W.hom).symm

/-- The actual scheme map from a comma chart to the constructed affine spectrum atlas. -/
def relativeSpectrumAtlasCommaToSpectrum (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumDescentAtlasHomToX A)).obj W))
      (smallEtaleToSpaces (ofOver (relativeSpectrumDescentAtlas A))).op) :
    a.right.unop.left ⟶ relativeSpectrumDescentAtlas A :=
  yoneda.preimage a.right.unop.hom

/-- The actual scheme map from a comma chart to the étale test chart. -/
def relativeSpectrumAtlasCommaToChart (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumDescentAtlasHomToX A)).obj W))
      (smallEtaleToSpaces (ofOver (relativeSpectrumDescentAtlas A))).op) :
    a.right.unop.left ⟶ W.left :=
  yoneda.preimage (a.hom.unop.left ≫ etaleBaseChangeSnd (relativeSpectrumDescentAtlasHomToX A) W)

/-- The represented overlap receives the two actual comma-chart maps. -/
def relativeSpectrumAtlasCommaToOverlap (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumDescentAtlasHomToX A)).obj W))
      (smallEtaleToSpaces (ofOver (relativeSpectrumDescentAtlas A))).op) :
    a.right.unop.left ⟶ (relativeSpectrumAtlasOverlapChart X W).left :=
  yoneda.preimage (((atlasHom_presheaf_etale X).rep.isPullback W.hom).lift
    (yoneda.map (relativeSpectrumAtlasCommaToSpectrum A W a ≫
      Over.homMk (Scheme.relativeSpectrumOver (onChart A (relativeSpectrumAtlasChart X))).π rfl))
    (yoneda.map (relativeSpectrumAtlasCommaToChart A W a)) sorry)

/-- The comma-chart maps satisfy the actual spectrum/overlap structural triangle. -/
theorem relativeSpectrumAtlasComma_triangle (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpectrumDescentAtlasHomToX A)).obj W))
      (smallEtaleToSpaces (ofOver (relativeSpectrumDescentAtlas A))).op) :
    (relativeSpectrumAtlasCommaToSpectrum A W a).left ≫
        (Scheme.relativeSpectrumOver (onChart A (relativeSpectrumAtlasChart X))).π =
      (relativeSpectrumAtlasCommaToOverlap A W a).left ≫
        (relativeSpectrumAtlasOverlapToAtlas X W).left.left := sorry

/-- Compatible section evaluations over the canonical direct-image chart index. -/
def relativeSpectrumAtlasAlgebraCone (A : X.QcAlgebraUnder) (W : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange (relativeSpectrumDescentAtlasHomToX A)).obj W))
      (smallEtaleToSpaces (ofOver (relativeSpectrumDescentAtlas A))).op ⋙
        (commStructureSheaf (ofOver (relativeSpectrumDescentAtlas A))).obj) where
  pt := sectionRing A W
  π :=
    { app := fun a ↦ A.obj.right.obj.map (relativeSpectrumAtlasOverlapToChart X W).op ≫
        relativeSpectrumGluedPointEvaluation A (relativeSpectrumAtlasOverlapToAtlas X W)
          (relativeSpectrumAtlasCommaToOverlap A W a).left
          (relativeSpectrumAtlasCommaToSpectrum A W a).left
          (relativeSpectrumAtlasComma_triangle A W a)
      naturality := sorry }

/-- The constructed spectrum atlas carries a genuine global O_X-algebra map from A. -/
def relativeSpectrumAtlasAlgebraMap (A : X.QcAlgebraUnder) :
    A.obj ⟶ Under.mk (commStructureSheafMap (relativeSpectrumDescentAtlasHomToX A)) :=
  Under.homMk
    ⟨{ app := fun W ↦ ConormalAlgebra.commRingPushforwardConeLift
          (relativeSpectrumDescentAtlasHomToX A)
          (commStructureSheaf (ofOver (relativeSpectrumDescentAtlas A))) W.unop
          (relativeSpectrumAtlasAlgebraCone A W.unop)
       naturality := sorry }⟩ sorry

end AlgebraicGeometry.AlgebraicSpace
