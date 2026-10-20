module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.AtlasPoint
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.PointMap

/-!
# Reconstruct the local atlas lift of an original relative-spectrum point

Pull the supplied atlas back along the point's actual base map. On each affine
atlas open, evaluate the supplied descended algebra-map component on the real
pullback chart, then glue those ring maps into the point on the concrete atlas
spectrum. No inverse of the global restriction-bijectivity theorem is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The actual base arrow of the original relative-spectrum point. -/
def relativeSpectrumPointBase (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) : ofOver T ⟶ X :=
  yonedaEquiv.symm p.1

/-- Pull the stored atlas back along the point's base arrow using its supplied representability data. -/
def relativeSpectrumPointAtlasOver (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) : Over S :=
  (atlasHom_presheaf_etale X).rep.pullback (relativeSpectrumPointBase A p)

/-- The actual projection of the point's atlas pullback to the stored atlas. -/
def relativeSpectrumPointAtlasToAtlas (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumPointAtlasOver A p ⟶ atlasScheme X :=
  (atlasHom_presheaf_etale X).rep.fst' (relativeSpectrumPointBase A p)

/-- The actual projection of the point's atlas pullback to its test scheme. -/
def relativeSpectrumPointAtlasToTest (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumPointAtlasOver A p ⟶ T :=
  (atlasHom_presheaf_etale X).rep.snd (relativeSpectrumPointBase A p)

/-- The inverse-image scheme of an atlas open, viewed over S. -/
def relativeSpectrumPointAtlasOpenOver (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) : Over S :=
  Over.mk (((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).ι ≫
    (relativeSpectrumPointAtlasOver A p).hom)

/-- The pulled-back atlas open as an actual étale chart of the test scheme. -/
def relativeSpectrumPointAtlasOpenChart (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) : smallEtaleSite (ofOver T) :=
  @smallEtaleSite.mk S (ofOver T) (relativeSpectrumPointAtlasOpenOver A p P)
    ((ofOverFunctor S).map (Over.homMk
      (((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).ι ≫
        (relativeSpectrumPointAtlasToTest A p).left) sorry)) sorry

/-- The pullback open's actual scheme map to the corresponding atlas open. -/
def relativeSpectrumPointAtlasOpenToAtlasOpen (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) :
    relativeSpectrumPointAtlasOpenOver A p P ⟶ atlasOpenOver X P :=
  Over.homMk ((relativeSpectrumPointAtlasToAtlas A p).left ∣_ P) sorry

/-- The actual morphism from the pullback open into the space-étale base-change object. -/
def relativeSpectrumPointAtlasOpenEvaluationArrow (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) (P : (atlasScheme X).left.Opens) :
    (smallEtaleToSpaces (ofOver T)).obj (relativeSpectrumPointAtlasOpenChart A p P) ⟶
      (etaleBaseChange (relativeSpectrumPointBase A p)).obj (atlasOpenToSmallEtaleObj X P) :=
  MorphismProperty.Over.homMk
    ((pullback.lift (relativeSpectrumPointAtlasOpenChart A p P).hom
      ((ofOverFunctor S).map (relativeSpectrumPointAtlasOpenToAtlasOpen A p P)) sorry :
        yoneda.obj (relativeSpectrumPointAtlasOpenOver A p P) ⟶
          (etaleBaseChangeSpace (relativeSpectrumPointBase A p)
            (atlasOpenToSmallEtaleObj X P)).functorOfPoints)) sorry

/-- The point's actual descended atlas component evaluated on its represented pullback open. -/
def relativeSpectrumPointAtlasSectionMap (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) :
    sectionRing A (atlasOpenToSmallEtaleObj X P) ⟶
      Γ(((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).toScheme, ⊤) :=
  p.2.1.right.app (op P) ≫
    commRingPushforwardEvaluation (relativeSpectrumPointBase A p) (commStructureSheaf (ofOver T))
      (relativeSpectrumPointAtlasOpenEvaluationArrow A p P)

/-- The actual algebra map on the atlas pullback, glued from the supplied point's original components. -/
def relativeSpectrumPointAtlasAlgebraMap (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    (onChart A (relativeSpectrumAtlasChart X)).obj ⟶ Under.mk
      (Hom.commRingSheafPushforwardMap (relativeSpectrumPointAtlasToAtlas A p).left.toShHom) :=
  Under.homMk
    ⟨{ app := fun P ↦ relativeSpectrumPointAtlasSectionMap A p P.unop ≫
        (Scheme.Opens.topIso ((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P.unop)).hom
       naturality := sorry }⟩ sorry

/-- The actual lift of the original point to the concrete affine spectrum atlas. -/
def relativeSpectrumPointAtlasLift (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumPointAtlasOver A p ⟶ relativeSpectrumDescentAtlas A :=
  Over.homMk
    (Scheme.relativeSpectrumPointMap (onChart A (relativeSpectrumAtlasChart X))
      ⟨(relativeSpectrumPointAtlasToAtlas A p).left, relativeSpectrumPointAtlasAlgebraMap A p⟩) sorry

/-- The local atlas lift is over the original test point's base morphism. -/
theorem relativeSpectrumPointAtlasLift_toX (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    (ofOverFunctor S).map (relativeSpectrumPointAtlasLift A p) ≫ relativeSpectrumDescentAtlasHomToX A =
      (ofOverFunctor S).map (relativeSpectrumPointAtlasToTest A p) ≫ relativeSpectrumPointBase A p := sorry

end AlgebraicGeometry.AlgebraicSpace
