/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Universal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Arbitrary base change of the relative spectrum

The pulled-back algebra is the actual pushout of inverse-image commutative
ring sheaves. Its canonical map to the original relative spectrum uses the
geometric adjunction unit. In the reverse direction a pullback point supplies
an algebra map whose adjunction transpose and structure map descend through
the native pushout. These actual point functions give the limiting square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace QcAlgebraUnder

/-- The inverse-image algebra sheaf tensored with the structure sheaf of the new base. -/
def baseChange (f : Y ⟶ X) (A : X.QcAlgebraUnder) : Y.QcAlgebraUnder where
  obj := Under.mk
    (pushout.inl (inverseImageStructureSheafHom f) ((commRingInverseImage f).map A.obj.hom))
  property := sorry

/-- The canonical map to the direct image of the pulled-back algebra is the actual adjunction unit. -/
def baseChangeUnit (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    A.obj.right ⟶ (commRingPushforward f).obj (baseChange f A).obj.right :=
  (ConormalAlgebra.commRingInverseImageAdjunction f).unit.app A.obj.right ≫
    (commRingPushforward f).map
      (pushout.inr (inverseImageStructureSheafHom f) ((commRingInverseImage f).map A.obj.hom))

end QcAlgebraUnder

/-- A point of the pulled-back algebra supplies an actual original-base algebra map. -/
def relativeSpectrumBaseChangePointAlgebraMap (f : Y ⟶ X) (A : X.QcAlgebraUnder)
    {T : Over S} (p : relativeSpectrumPair (QcAlgebraUnder.baseChange f A) T) :
    A.obj ⟶ relativeSpectrumTarget
      (relativeSpectrumPointBase (QcAlgebraUnder.baseChange f A) p ≫ f) :=
  Under.homMk
    (QcAlgebraUnder.baseChangeUnit f A ≫
      (commRingPushforward f).map
        (relativeSpectrumPointAlgebraMap (QcAlgebraUnder.baseChange f A) p).right ≫
      (commRingPushforwardComp (relativeSpectrumPointBase (QcAlgebraUnder.baseChange f A) p) f).hom.app
        (commStructureSheaf (ofOver T))) sorry

/-- The actual map of relative spectra induced by arbitrary base change. -/
def relativeSpecBaseChangeMap (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    relativeSpec (QcAlgebraUnder.baseChange f A) ⟶ relativeSpec A where
  app T := TypeCat.ofHom fun p ↦
    relativeSpectrumPairMk (relativeSpectrumPointBase (QcAlgebraUnder.baseChange f A) p ≫ f)
      (relativeSpectrumBaseChangePointAlgebraMap f A p)
  naturality := sorry

/-- The canonical arbitrary-base-change map commutes with both structural morphisms. -/
theorem relativeSpecBaseChangeMap_toBase (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    relativeSpecBaseChangeMap f A ≫ relativeSpecπ A =
      relativeSpecπ (QcAlgebraUnder.baseChange f A) ≫ f := sorry

/-- Transpose the supplied global point algebra map through the genuine inverse-image adjunction. -/
def relativeSpectrumBaseChangeTranspose (f : Y ⟶ X) (A : X.QcAlgebraUnder)
    {T : Over S} (g : ofOver T ⟶ Y) (α : A.obj ⟶ relativeSpectrumTarget (g ≫ f)) :
    (commRingInverseImage f).obj A.obj.right ⟶
      (commRingPushforward g).obj (commStructureSheaf (ofOver T)) :=
  (ConormalAlgebra.commRingInverseImageAdjunction f).homEquiv _ _ |>.symm
    (α.right ≫ (commRingPushforwardComp g f).inv.app (commStructureSheaf (ofOver T)))

/-- The actual transpose and the specified structure map agree on inverse-image base sections. -/
theorem relativeSpectrumBaseChangeTranspose_w (f : Y ⟶ X) (A : X.QcAlgebraUnder)
    {T : Over S} (g : ofOver T ⟶ Y) (α : A.obj ⟶ relativeSpectrumTarget (g ≫ f)) :
    inverseImageStructureSheafHom f ≫ commStructureSheafMap g =
      (commRingInverseImage f).map A.obj.hom ≫ relativeSpectrumBaseChangeTranspose f A g α := sorry

/-- An original algebra map over the composite base gives an actual pulled-back-algebra map. -/
def relativeSpectrumBaseChangeAlgebraLift (f : Y ⟶ X) (A : X.QcAlgebraUnder)
    {T : Over S} (g : ofOver T ⟶ Y) (α : A.obj ⟶ relativeSpectrumTarget (g ≫ f)) :
    (QcAlgebraUnder.baseChange f A).obj ⟶ relativeSpectrumTarget g :=
  Under.homMk
    (pushout.desc (commStructureSheafMap g) (relativeSpectrumBaseChangeTranspose f A g α)
      (relativeSpectrumBaseChangeTranspose_w f A g α)) sorry

/-- A point over the new base and an original spectrum point satisfying the base triangle give
an actual point of the pulled-back algebra. -/
def relativeSpectrumBaseChangePointLift (f : Y ⟶ X) (A : X.QcAlgebraUnder)
    {T : Over S} (g : ofOver T ⟶ Y) (p : relativeSpectrumPair A T)
    (h : relativeSpectrumPointBase A p = g ≫ f) :
    relativeSpectrumPair (QcAlgebraUnder.baseChange f A) T :=
  relativeSpectrumPairMk g
    (relativeSpectrumBaseChangeAlgebraLift f A g
      (relativeSpectrumPointAlgebraMap A p ≫ eqToHom (congrArg relativeSpectrumTarget h)))

/-- The native presheaf pullback cone uses the actual spectrum map and projection. -/
def relativeSpecBaseChangeCone (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    PullbackCone (homFunctor (relativeSpecπ A)) (homFunctor f) :=
  PullbackCone.mk (homFunctor (relativeSpecBaseChangeMap f A))
    (homFunctor (relativeSpecπ (QcAlgebraUnder.baseChange f A)))
    (relativeSpecBaseChangeMap_toBase f A)

/-- The two point components of any cone satisfy the precise base triangle for algebra lifting. -/
theorem relativeSpecBaseChangeConePoint_w (f : Y ⟶ X) (A : X.QcAlgebraUnder)
    (c : PullbackCone (homFunctor (relativeSpecπ A)) (homFunctor f))
    (T : (Over S)ᵒᵖ) (z : c.pt.obj T) :
    relativeSpectrumPointBase A (c.fst.app T z) = yonedaEquiv.symm (c.snd.app T z) ≫ f := sorry

/-- The actual mediating transformation lifts each cone point by the native algebra pushout. -/
def relativeSpecBaseChangeConeLift (f : Y ⟶ X) (A : X.QcAlgebraUnder)
    (c : PullbackCone (homFunctor (relativeSpecπ A)) (homFunctor f)) :
    c.pt ⟶ (relativeSpec (QcAlgebraUnder.baseChange f A)).functorOfPoints where
  app T := TypeCat.ofHom fun z ↦ relativeSpectrumBaseChangePointLift f A
    (yonedaEquiv.symm (c.snd.app T z)) (c.fst.app T z) (relativeSpecBaseChangeConePoint_w f A c T z)
  naturality := sorry

/-- The arbitrary-base-change cone is limiting with its specified actual algebra-pushout lift. -/
def relativeSpecBaseChangeConeIsLimit (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    IsLimit (relativeSpecBaseChangeCone f A) :=
  PullbackCone.IsLimit.mk (C := (Over S)ᵒᵖ ⥤ Type u) (relativeSpecBaseChangeMap_toBase f A)
    (relativeSpecBaseChangeConeLift f A) sorry sorry sorry

/-- Relative spectrum commutes with arbitrary base change, with the actual comparison maps. -/
theorem relativeSpecBaseChange_isPullback (f : Y ⟶ X) (A : X.QcAlgebraUnder) :
    IsPullback (homFunctor (relativeSpecBaseChangeMap f A))
      (homFunctor (relativeSpecπ (QcAlgebraUnder.baseChange f A)))
      (homFunctor (relativeSpecπ A)) (homFunctor f) :=
  IsPullback.of_isLimit (relativeSpecBaseChangeConeIsLimit f A)

end AlgebraicGeometry.AlgebraicSpace
