/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Reconstruction

/-!
# Universal algebra maps and the relative-spectrum hom correspondence

Evaluate each actual scheme-valued spectrum point's reconstructed algebra map
on direct-image comma charts. The canonical chart-cone lift assembles these
values into the universal algebra map. The hom correspondence uses this map
in one direction and the original point constructor in the other. Its inverse
recovers coefficients on affine section spectra of atlas overlaps and glues
them in the supplied algebra sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A test point projects to the base morphism obtained by composing with the spectrum projection. -/
theorem relativeSpecPoint_base (A : X.QcAlgebraUnder) {T : Over S}
    (t : ofOver T ⟶ relativeSpec A) :
    relativeSpectrumPointBase A (yonedaEquiv t) = t ≫ relativeSpecπ A := sorry

/-- The actual global algebra map carried by a supplied scheme-valued spectrum point. -/
def relativeSpecPointAlgebraMap (A : X.QcAlgebraUnder) {T : Over S}
    (t : ofOver T ⟶ relativeSpec A) : A.obj ⟶ relativeSpectrumTarget (t ≫ relativeSpecπ A) :=
  relativeSpectrumPointAlgebraMap A (yonedaEquiv t) ≫
    eqToHom (congrArg relativeSpectrumTarget (relativeSpecPoint_base A t))

/-- Restrict direct-image structure sections to the supplied scheme-valued test point. -/
def pushforwardStructureTest {Y : AlgebraicSpace S} (q : Y ⟶ X)
    {T : Over S} (t : ofOver T ⟶ Y) :
    (commRingPushforward q).obj (commStructureSheaf Y) ⟶
      (commRingPushforward (t ≫ q)).obj (commStructureSheaf (ofOver T)) :=
  (commRingPushforward q).map (commStructureSheafMap t) ≫
    commRingPushforwardPrecomp t q

/-- The actual spectrum point defined by a direct-image comma scheme chart. -/
def relativeSpecUniversalCommaPoint (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpecπ A)).obj W))
      (smallEtaleToSpaces (relativeSpec A)).op) :
    ofOver a.right.unop.left ⟶ relativeSpec A :=
  a.right.unop.hom

/-- The actual arrow from the comma scheme to the base's étale chart. -/
def relativeSpecUniversalCommaToChart (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpecπ A)).obj W))
      (smallEtaleToSpaces (relativeSpec A)).op) : a.right.unop.left ⟶ W.left :=
  yoneda.preimage (a.hom.unop.left ≫ etaleBaseChangeSnd (relativeSpecπ A) W)

/-- The identity scheme chart used to evaluate the actual point's direct-image algebra map. -/
def relativeSpecUniversalCommaIdentityChart (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpecπ A)).obj W))
      (smallEtaleToSpaces (relativeSpec A)).op) : smallEtaleSite (ofOver a.right.unop.left) :=
  smallEtaleSite.mk (𝟙 (ofOver a.right.unop.left))

/-- The comma scheme's two actual arrows give an evaluation arrow into its base-chart pullback. -/
def relativeSpecUniversalCommaEvaluationArrow (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpecπ A)).obj W))
      (smallEtaleToSpaces (relativeSpec A)).op) :
    (smallEtaleToSpaces (ofOver a.right.unop.left)).obj
        (relativeSpecUniversalCommaIdentityChart A W a) ⟶
      (etaleBaseChange (relativeSpecUniversalCommaPoint A W a ≫ relativeSpecπ A)).obj W :=
  MorphismProperty.Over.homMk
    ((pullback.lift (relativeSpecUniversalCommaIdentityChart A W a).hom
      (ofOverMap (relativeSpecUniversalCommaToChart A W a)) sorry :
      yoneda.obj a.right.unop.left ⟶
        (etaleBaseChangeSpace (relativeSpecUniversalCommaPoint A W a ≫ relativeSpecπ A) W).functorOfPoints))
    sorry

/-- Evaluate the given point's actual algebra map on the comma scheme itself. -/
def relativeSpecUniversalCommaSectionMap (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (a : StructuredArrow (op ((etaleBaseChange (relativeSpecπ A)).obj W))
      (smallEtaleToSpaces (relativeSpec A)).op) :
    QcAlgebraUnder.sectionRing A W ⟶ (commStructureSheaf (relativeSpec A)).obj.obj (op a.right.unop) := by
  change QcAlgebraUnder.sectionRing A W ⟶ Scheme.Γ.obj (op a.right.unop.left.left)
  let evaluation :
      ((commRingPushforward (relativeSpecUniversalCommaPoint A W a ≫ relativeSpecπ A)).obj
        (commStructureSheaf (ofOver a.right.unop.left))).obj.obj (op W) ⟶
      Scheme.Γ.obj (op a.right.unop.left.left) :=
    commRingPushforwardEvaluation (relativeSpecUniversalCommaPoint A W a ≫ relativeSpecπ A)
      (commStructureSheaf (ofOver a.right.unop.left)) (relativeSpecUniversalCommaEvaluationArrow A W a)
  exact (InducedCategory.Hom.hom
      (relativeSpecPointAlgebraMap A (relativeSpecUniversalCommaPoint A W a)).right).app (op W) ≫ evaluation

/-- The actual universal evaluations form the cone defining direct-image sections. -/
def relativeSpecUniversalAlgebraCone (A : X.QcAlgebraUnder) (W : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange (relativeSpecπ A)).obj W))
      (smallEtaleToSpaces (relativeSpec A)).op ⋙ (commStructureSheaf (relativeSpec A)).obj) where
  pt := QcAlgebraUnder.sectionRing A W
  π := { app := fun a ↦ relativeSpecUniversalCommaSectionMap A W a, naturality := sorry }

/-- The universal algebra map is assembled from actual scheme-valued point evaluations. -/
def relativeSpecUniversalAlgebraMap (A : X.QcAlgebraUnder) :
    A.obj ⟶ Under.mk (commStructureSheafMap (relativeSpecπ A)) :=
  Under.homMk
    ⟨{ app := fun W ↦ ConormalAlgebra.commRingPushforwardConeLift (relativeSpecπ A)
          (commStructureSheaf (relativeSpec A)) W.unop (relativeSpecUniversalAlgebraCone A W.unop)
       naturality := sorry }⟩ sorry

/-- Universal sections restrict to the actual algebra map of every supplied test point. -/
theorem relativeSpecUniversalAlgebraMap_test (A : X.QcAlgebraUnder) {T : Over S}
    (t : ofOver T ⟶ relativeSpec A) :
    (relativeSpecUniversalAlgebraMap A).right ≫ pushforwardStructureTest (relativeSpecπ A) t =
      (relativeSpecPointAlgebraMap A t).right := sorry

/-- The universal algebra map is bijective on every étale chart's sections. -/
theorem relativeSpecUniversalAlgebraMap_app_bijective (A : X.QcAlgebraUnder)
    (W : (smallEtaleSite X)ᵒᵖ) :
    Function.Bijective ((InducedCategory.Hom.hom (relativeSpecUniversalAlgebraMap A).right).app W).hom :=
  sorry

/-- The affine opens of the atlas overlap, regarded as a covering family of the base chart. -/
def relativeSpecUniversalInverseCoverMap (W : smallEtaleSite X)
    (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens) :
    (chartOpens (relativeSpectrumAtlasOverlapChart X W)).obj
        (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.Opens) ⟶ W :=
  relativeSpectrumOpenChartInclusion (relativeSpectrumAtlasOverlapChart X W) Q ≫
    relativeSpectrumAtlasOverlapToChart X W

/-- An affine section spectrum is an actual affine piece of the overlap's native spectrum. -/
def relativeSpecUniversalInverseAffineOver (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens) : Over S :=
  Over.mk (colimit.ι
    (Scheme.relativeSpectrumNativeGluingData (onChart A (relativeSpectrumAtlasOverlapChart X W))).functor Q ≫
      (relativeSpectrumChartOver A (relativeSpectrumAtlasOverlapChart X W)).hom)

/-- The affine spectrum maps to the original relative spectrum through its specified atlas. -/
def relativeSpecUniversalInverseAffineChart (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens) :
    smallEtaleSite (relativeSpec A) :=
  @smallEtaleSite.mk S (relativeSpec A) (relativeSpecUniversalInverseAffineOver A W Q)
    (ofOverMap
      ((Over.homMk (colimit.ι
          (Scheme.relativeSpectrumNativeGluingData
            (onChart A (relativeSpectrumAtlasOverlapChart X W))).functor Q) rfl :
          relativeSpecUniversalInverseAffineOver A W Q ⟶
            relativeSpectrumChartOver A (relativeSpectrumAtlasOverlapChart X W)) ≫
        relativeSpectrumChartOverMap A (relativeSpectrumAtlasOverlapToAtlas X W)) ≫
      relativeSpecAtlas A) sorry

/-- The same affine piece maps to the base chart through the overlap projection. -/
def relativeSpecUniversalInverseAffineToBase (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens) :
    relativeSpecUniversalInverseAffineOver A W Q ⟶ W.left :=
  Over.homMk (colimit.ι
    (Scheme.relativeSpectrumNativeGluingData
      (onChart A (relativeSpectrumAtlasOverlapChart X W))).functor Q ≫
    (Scheme.relativeSpectrumOver (onChart A (relativeSpectrumAtlasOverlapChart X W))).π ≫
    (relativeSpectrumAtlasOverlapToChart X W).left.left) sorry

/-- The two specified affine-piece maps give a chart of the direct-image fibre product. -/
def relativeSpecUniversalInverseAffineEvaluationArrow (A : X.QcAlgebraUnder)
    (W : smallEtaleSite X)
    (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens) :
    (smallEtaleToSpaces (relativeSpec A)).obj (relativeSpecUniversalInverseAffineChart A W Q) ⟶
      (etaleBaseChange (relativeSpecπ A)).obj W :=
  MorphismProperty.Over.homMk
    ((pullback.lift (relativeSpecUniversalInverseAffineChart A W Q).hom
      (ofOverMap (relativeSpecUniversalInverseAffineToBase A W Q)) sorry :
      yoneda.obj (relativeSpecUniversalInverseAffineOver A W Q) ⟶
        (etaleBaseChangeSpace (relativeSpecπ A) W).functorOfPoints)) sorry

/-- Evaluate on an actual affine section spectrum and recover its coefficients by `ΓSpecIso`. -/
def relativeSpecUniversalInverseAffineMap (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens) :
    ((commRingPushforward (relativeSpecπ A)).obj (commStructureSheaf (relativeSpec A))).obj.obj (op W) ⟶
      sectionRing A ((chartOpens (relativeSpectrumAtlasOverlapChart X W)).obj
        (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.Opens)) :=
  commRingPushforwardEvaluation (relativeSpecπ A) (commStructureSheaf (relativeSpec A))
      (relativeSpecUniversalInverseAffineEvaluationArrow A W Q) ≫
    (Scheme.ΓSpecIso (sectionRing A ((chartOpens (relativeSpectrumAtlasOverlapChart X W)).obj
      (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.Opens)))).hom

/-- Affine opens of the atlas pullback cover the original étale chart. -/
theorem relativeSpecUniversalInverseCover_mem (W : smallEtaleSite X) :
    Sieve.ofArrows _ (relativeSpecUniversalInverseCoverMap W) ∈ (smallEtaleTopology X) W := sorry

/-- The affine coefficient maps agree on every common étale refinement. -/
theorem relativeSpecUniversalInverseAffineMap_compatible (A : X.QcAlgebraUnder)
    (W : smallEtaleSite X) {E : smallEtaleSite X}
    {Q Q' : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens}
    (a : E ⟶ (chartOpens (relativeSpectrumAtlasOverlapChart X W)).obj
      (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.Opens))
    (b : E ⟶ (chartOpens (relativeSpectrumAtlasOverlapChart X W)).obj
      (Q' : (relativeSpectrumAtlasOverlapChart X W).left.left.Opens))
    (h : a ≫ relativeSpecUniversalInverseCoverMap W Q =
      b ≫ relativeSpecUniversalInverseCoverMap W Q') :
    relativeSpecUniversalInverseAffineMap A W Q ≫ A.obj.right.obj.map a.op =
      relativeSpecUniversalInverseAffineMap A W Q' ≫ A.obj.right.obj.map b.op := sorry

/-- Glue the actual affine coefficient maps in the supplied algebra sheaf. -/
def relativeSpecUniversalInverseChartMap (A : X.QcAlgebraUnder) (W : smallEtaleSite X) :
    ((commRingPushforward (relativeSpecπ A)).obj (commStructureSheaf (relativeSpec A))).obj.obj (op W) ⟶
      sectionRing A W :=
  A.obj.right.property.amalgamateOfArrows (relativeSpecUniversalInverseCoverMap W)
    (relativeSpecUniversalInverseCover_mem W) (relativeSpecUniversalInverseAffineMap A W)
    (by
      intro E Q Q' a b h
      exact relativeSpecUniversalInverseAffineMap_compatible A W a b h)

/-- The glued inverse restricts to the specified coefficient map on each affine overlap chart. -/
@[reassoc (attr := simp)]
theorem relativeSpecUniversalInverseChartMap_restrict (A : X.QcAlgebraUnder) (W : smallEtaleSite X)
    (Q : (relativeSpectrumAtlasOverlapChart X W).left.left.affineOpens) :
    relativeSpecUniversalInverseChartMap A W ≫
        A.obj.right.obj.map (relativeSpecUniversalInverseCoverMap W Q).op =
      relativeSpecUniversalInverseAffineMap A W Q :=
  A.obj.right.property.amalgamateOfArrows_map (relativeSpecUniversalInverseCoverMap W)
    (relativeSpecUniversalInverseCover_mem W) (relativeSpecUniversalInverseAffineMap A W)
    (by
      intro E Q Q' a b h
      exact relativeSpecUniversalInverseAffineMap_compatible A W a b h) Q

/-- The inverse section function evaluates on affine spectra and glues their coefficients. -/
def relativeSpecUniversalInverseSection (A : X.QcAlgebraUnder) (W : (smallEtaleSite X)ᵒᵖ) :
    ((commRingPushforward (relativeSpecπ A)).obj (commStructureSheaf (relativeSpec A))).obj.obj W →
      A.obj.right.obj.obj W :=
  (relativeSpecUniversalInverseChartMap A W.unop).hom

/-- The fixed inverse function recovers every original algebra section. -/
@[simp]
theorem relativeSpecUniversalInverseSection_apply (A : X.QcAlgebraUnder)
    (W : (smallEtaleSite X)ᵒᵖ) (a : A.obj.right.obj.obj W) :
    relativeSpecUniversalInverseSection A W
      (((InducedCategory.Hom.hom (relativeSpecUniversalAlgebraMap A).right).app W).hom a) = a := sorry

/-- Every direct-image section is the universal image of its specified inverse section. -/
@[simp]
theorem relativeSpecUniversalAlgebraMap_apply_inverseSection (A : X.QcAlgebraUnder)
    (W : (smallEtaleSite X)ᵒᵖ)
    (s : ((commRingPushforward (relativeSpecπ A)).obj (commStructureSheaf (relativeSpec A))).obj.obj W) :
    ((InducedCategory.Hom.hom (relativeSpecUniversalAlgebraMap A).right).app W).hom
      (relativeSpecUniversalInverseSection A W s) = s := sorry

/-- The inverse ring homomorphism is the amalgamation of actual affine coefficient maps. -/
def relativeSpecUniversalInverseRingHom (A : X.QcAlgebraUnder) (W : (smallEtaleSite X)ᵒᵖ) :
    ((commRingPushforward (relativeSpecπ A)).obj (commStructureSheaf (relativeSpec A))).obj.obj W →+*
      A.obj.right.obj.obj W :=
  (relativeSpecUniversalInverseChartMap A W.unop).hom

/-- The actual inverse sheaf-algebra map, defined from the fixed section maps. -/
def relativeSpecUniversalAlgebraInverse (A : X.QcAlgebraUnder) :
    Under.mk (commStructureSheafMap (relativeSpecπ A)) ⟶ A.obj :=
  Under.homMk
    ⟨{ app := fun W ↦ relativeSpecUniversalInverseChartMap A W.unop
       naturality := sorry }⟩ sorry

/-- The algebra/direct-image identification has specified actual hom and inverse maps. -/
def relativeSpecUniversalAlgebraIso (A : X.QcAlgebraUnder) :
    A.obj ≅ Under.mk (commStructureSheafMap (relativeSpecπ A)) where
  hom := relativeSpecUniversalAlgebraMap A
  inv := relativeSpecUniversalAlgebraInverse A
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The global algebra map of a spectrum morphism is its actual universal-map pullback. -/
def relativeSpecHomAlgebra {Y : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (t : Y ⟶ relativeSpec A) :
    A.obj ⟶ Under.mk (commStructureSheafMap (t ≫ relativeSpecπ A)) :=
  Under.homMk ((relativeSpecUniversalAlgebraMap A).right ≫
    (commRingPushforward (relativeSpecπ A)).map (commStructureSheafMap t) ≫
      (commRingPushforwardComp t (relativeSpecπ A)).hom.app (commStructureSheaf Y)) sorry

/-- The actual algebraic-space morphism induced by a base map and a global algebra map. -/
def relativeSpecHomOfAlgebra {Y : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (g : Y ⟶ X) (α : A.obj ⟶ Under.mk (commStructureSheafMap g)) : Y ⟶ relativeSpec A where
  app T := TypeCat.ofHom fun y ↦
    let t : ofOver T.unop ⟶ Y := yonedaEquiv.symm y
    relativeSpectrumPairMk (t ≫ g)
      (Under.homMk (α.right ≫ (commRingPushforward g).map (commStructureSheafMap t) ≫
        (commRingPushforwardComp t g).hom.app (commStructureSheaf (ofOver T.unop))) sorry)
  naturality := sorry

/-- The induced spectrum morphism has exactly the given base arrow. -/
theorem relativeSpecHomOfAlgebra_toBase {Y : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (g : Y ⟶ X) (α : A.obj ⟶ Under.mk (commStructureSheafMap g)) :
    relativeSpecHomOfAlgebra A g α ≫ relativeSpecπ A = g := sorry

/-- The hom correspondence uses actual universal-map pullback and pointwise algebra-map construction. -/
def relativeSpecHomEquiv (A : X.QcAlgebraUnder) (Y : AlgebraicSpace S) :
    (Y ⟶ relativeSpec A) ≃
      Σ g : Y ⟶ X, A.obj ⟶ Under.mk (commStructureSheafMap g) where
  toFun t := ⟨t ≫ relativeSpecπ A, relativeSpecHomAlgebra A t⟩
  invFun p := relativeSpecHomOfAlgebra A p.1 p.2
  left_inv := sorry
  right_inv := sorry

end AlgebraicGeometry.AlgebraicSpace
