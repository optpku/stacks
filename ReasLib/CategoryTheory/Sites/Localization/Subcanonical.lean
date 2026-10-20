module


public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
public import ReasLib.CategoryTheory.RepresentablePresheaf.Elements.OverEquivalence

/-! # Representable slice comparison with small coefficients

The category-of-elements equivalence works at the hom universe, so no resizing
axiom is needed for small étale sheaves of `Type u`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.SubcanonicalSlice

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/-- The representable-elements equivalence identifies the elements topology with
the ordinary slice topology: both coverings are detected after projection to `C`. -/
instance elementsOver_dense (U : C) :
    (RepresentablePresheaf.Elements.overEquivalence U).symm.inverse.IsDenseSubsite
      (localizationTopology (J.yoneda.obj U)) (J.over U) :=
  sorry

/-- The concrete representable localization equivalence at the hom universe. -/
def equivalence (U : C) : Sheaf (J.over U) (Type v) ≌ Over (J.yoneda.obj U) :=
  ((RepresentablePresheaf.Elements.overEquivalence U).symm.sheafCongr
    (J.over U) (localizationTopology (J.yoneda.obj U)) (Type v)).trans
      (sheafCategoryOfElementsEquivOver (J.yoneda.obj U))

/-- The representable comparison is the composite of the site equivalence and
the explicit collection/fibre equivalence of presheaves, restricted to sheaves. -/
theorem equivalence_functor (U : C) :
    (equivalence J U).functor =
      ((RepresentablePresheaf.Elements.overEquivalence U).symm.sheafCongr
        (J.over U) (localizationTopology (J.yoneda.obj U)) (Type v)).functor ⋙
          (sheafCategoryOfElementsEquivOver (J.yoneda.obj U)).functor := rfl

/-- Continuity of the representable-elements projection into the slice. -/
instance elementsOver_continuous (U : C) :
    (RepresentablePresheaf.Elements.overEquivalence U).functor.IsContinuous
      (localizationTopology (J.yoneda.obj U)) (J.over U) :=
  sorry

/-- The projection underlying a representable-elements site is continuous. -/
instance representableProjection_continuous (U : C) :
    (CategoryOfElements.π (CategoryTheory.yoneda.obj U)).leftOp.IsContinuous
      (localizationTopology (J.yoneda.obj U)) J :=
  localizationProjection_isContinuous (J.yoneda.obj U)

/-- Representable localization carries slice restriction to the slice-product functor. -/
def restrictionIsoStar (U : C) :
    J.overPullback (Type v) U ⋙ (equivalence J U).functor ≅ Over.star (J.yoneda.obj U) :=
  Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp'
        (eqToIso (RepresentablePresheaf.Elements.overEquivalence.functor.comm U))
        (Type v) (localizationTopology (J.yoneda.obj U)) (J.over U) J)
      (sheafCategoryOfElementsEquivOver (J.yoneda.obj U)).functor ≪≫
    sheafCategoryOfElementsInverseImageIsoStar (J.yoneda.obj U)

/-- Returning from the sheaf slice carries slice-products to ordinary slice restriction. -/
def starInverseIso (U : C) :
    Over.star (J.yoneda.obj U) ⋙ (equivalence J U).inverse ≅ J.overPullback (Type v) U :=
  Functor.isoWhiskerRight (restrictionIsoStar J U).symm (equivalence J U).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (J.overPullback (Type v) U) (equivalence J U).unitIso.symm ≪≫
    Functor.rightUnitor _

end CategoryTheory.GrothendieckTopology.SubcanonicalSlice

