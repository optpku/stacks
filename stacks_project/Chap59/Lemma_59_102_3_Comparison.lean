module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Big
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap59.Lemma_59_102_3_Morphism

/-!
# Small-étale to big-ph pushforward comparisons

Canonical inverse-image squares and right mates identifying small étale direct
images with big ph direct images after the composite comparison
`a_S = π_S ∘ ε_S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Continuous sheaf pushforward along `Over.pullback f` on big ph sites is a
right adjoint, via the postcomposition-pullback adjunction. -/
instance isRightAdjoint_overPullback_sheafPushforwardContinuous_ph :
    ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
      (Scheme.bigPhSite Y) (Scheme.bigPhSite X)).IsRightAdjoint :=
  (Adjunction.sheafPushforwardContinuous (Over.mapPullbackAdj f)
    (Scheme.bigPhSite X) (Scheme.bigPhSite Y)).isRightAdjoint

/-- The composite `smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)` is continuous from the
small étale topology of `Y` to the big ph topology of `X`. -/
instance isContinuous_smallEtalePullback_comp_relocalization_ph :
    Functor.IsContinuous (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X))
      Y.smallEtaleTopology (Scheme.bigPhSite X) :=
  Functor.isContinuous_comp (smallEtalePullback f) (relocalizationFunctor (𝟙 X))
    Y.smallEtaleTopology X.smallEtaleTopology (Scheme.bigPhSite X)

/-- Site-level identification of the two paths around the small-étale / big-ph square. -/
noncomputable def smallPhRelocalizationSiteIso :
    smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X) ≅
      relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f :=
  (Functor.associator (smallEtalePullback f)
      (MorphismProperty.Over.forget (@Etale) ⊤ X) (Over.map (𝟙 X))).symm ≪≫
    Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f)
      (Over.map (𝟙 X)) ≪≫
    Functor.associator
      (MorphismProperty.Over.forget (@Etale) ⊤ Y) (Over.pullback f) (Over.map (𝟙 X)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      (Functor.isoWhiskerLeft (Over.pullback f) (Over.mapId X) ≪≫
        Functor.rightUnitor (Over.pullback f)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      ((Functor.leftUnitor (Over.pullback f)).symm ≪≫
        Functor.isoWhiskerRight (Over.mapId Y).symm (Over.pullback f)) ≪≫
    (Functor.associator (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      (Over.map (𝟙 Y)) (Over.pullback f)).symm

/-- The inverse image of the big ph morphism of topoi is the sheaf pullback along
`Over.pullback f`. -/
noncomputable def phBigInverseImageIsoPullback :
    (Ph.Big.morphismOfTopoi f)⁻¹ ≅
      (Over.pullback f).sheafPullback (Type (u + 1))
        (Scheme.bigPhSite Y) (Scheme.bigPhSite X) :=
  Adjunction.leftAdjointUniq
    (Adjunction.sheafPushforwardContinuous (Over.mapPullbackAdj f)
      (Scheme.bigPhSite X) (Scheme.bigPhSite Y))
    ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.bigPhSite Y) (Scheme.bigPhSite X))

section TypeSheaves

variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on sheaves of sets. -/
noncomputable def smallPhInverseImageSquare :
    (toSmallEtale Y)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f)⁻¹ ≅
      (smallMorphism f)⁻¹ ⋙ (toSmallEtale X)⁻¹ :=
  let adjA_Y :=
    (relocalizationFunctor (𝟙 Y)).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology (Scheme.bigPhSite Y)
  let adjA_X :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology (Scheme.bigPhSite X)
  let adjSmall :=
    (smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.bigPhSite Y) (Scheme.bigPhSite X)
  Functor.isoWhiskerLeft ((toSmallEtale Y)⁻¹) (phBigInverseImageIsoPullback f) ≪≫
    Functor.isoWhiskerRight (toSmallEtaleInverseImageIso Y)
      ((Over.pullback f).sheafPullback (Type (u + 1))
        (Scheme.bigPhSite Y) (Scheme.bigPhSite X)) ≪≫
    Adjunction.leftAdjointCompIso adjA_Y adjBigCont (adjSmall.comp adjA_X)
      (Functor.sheafPushforwardContinuousComp'
          (smallPhRelocalizationSiteIso f).symm (Type (u + 1))
          Y.smallEtaleTopology (Scheme.bigPhSite Y)
          (Scheme.bigPhSite X) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)))
          (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology
          (Scheme.bigPhSite X)).symm) ≪≫
    Functor.isoWhiskerLeft ((smallMorphism f)⁻¹) (toSmallEtaleInverseImageIso X).symm

/-- Canonical Type-valued mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,ph,* ∘ a_X⁻¹`. -/
noncomputable def smallPhPushforwardHom :
    (smallMorphism f).pushforward ⋙ (toSmallEtale Y)⁻¹ ⟶
      (toSmallEtale X)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallMorphism f).adjunction
    (Ph.Big.morphismOfTopoi f).adjunction
    (smallPhInverseImageSquare f)

/-- `smallPhPushforwardHom` is the right mate of the ph-small inverse-image square. -/
theorem smallPhPushforwardHom_eq :
    smallPhPushforwardHom f =
      DerivedBaseChange.map
        (smallMorphism f).adjunction
        (Ph.Big.morphismOfTopoi f).adjunction
        (smallPhInverseImageSquare f) :=
  sorry

end TypeSheaves

end AlgebraicGeometry.Scheme.PhComparison

end

end
