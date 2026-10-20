module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityRelocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.BaseChange

/-!
# Small-to-big étale direct-image comparisons

The canonical inverse-image square induces the small-to-big direct-image mate
on sheaves of sets. Big direct image on abelian sheaves also has a
cocontinuous presentation.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Adjunction
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor (associator isoWhiskerLeft isoWhiskerRight leftUnitor rightUnitor)
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

variable (f : Y ⟶ X)

section TypeSheaves

/-- Inverse image of the big étale morphism of topoi is sheaf pullback along `Over.pullback f`. -/
def bigInverseImageIsoPullback :
    (Big.morphismOfTopoi f)⁻¹ ≅
      (Over.pullback f).sheafPullback (Type (u + 1))
        (overEtaleTopology X) (overEtaleTopology Y) :=
  Adjunction.leftAdjointUniq
    (etaleTopology.overMapPushforwardAdjunction (Type (u + 1)) f)
    ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (overEtaleTopology X) (overEtaleTopology Y))

/-- Direct image along `π_X` identifies with restriction from `Over X` to the spaces étale
site followed by restriction along `smallEtaleToSpaces`. -/
private def typePiPushforwardIso (Z : AlgebraicSpace S) :
    (siteMorphismOfTopoi Z).pushforward ≅
      (MorphismProperty.Over.forget (@Etale S) ⊤ Z).sheafPushforwardContinuous
          (Type (u + 1)) (spacesEtaleTopology Z) (overEtaleTopology Z) ⋙
        (smallEtaleToSpaces Z).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology Z) (spacesEtaleTopology Z) :=
  isoWhiskerRight
    (Functor.sheafPushforwardContinuousIso
      (isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ Z) (Over.mapId Z) ≪≫
        rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ Z))
      (Type (u + 1)) (spacesEtaleTopology Z) (overEtaleTopology Z))
    ((smallEtaleToSpaces Z).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology Z) (spacesEtaleTopology Z))

/-- Restriction along the small étale inclusion is the inverse of cocontinuous extension. -/
private def typeInclusionRestrictIso (Z : AlgebraicSpace S) :
    (smallEtalePresentationRestriction Z) ≅
      (smallEtaleToSpaces Z).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Z) (spacesEtaleTopology Z) :=
  Adjunction.leftAdjointUniq
    (smallEtalePresentationEquivalence Z).symm.toAdjunction
    ((smallEtaleToSpaces Z).sheafAdjunctionCocontinuous (Type (u + 1))
      (smallEtaleTopology Z) (spacesEtaleTopology Z))

/-- Type-valued small étale pushforward agrees with cocontinuous extension followed by
evaluation along étale base change. -/
private def typeSmallPushforwardIso :
    (smallEtaleMorphismOfTopoi f).pushforward ≅ sheafPushforward (Type (u + 1)) f :=
  associator (smallEtaleInclusionDirectImage Y)
      ((spacesEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTopology Y))
      (smallEtalePresentationRestriction X) ≪≫
    isoWhiskerLeft (smallEtaleInclusionDirectImage Y)
      (isoWhiskerLeft
        ((spacesEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
          (spacesEtaleTopology X) (spacesEtaleTopology Y))
        (typeInclusionRestrictIso X)) ≪≫
    isoWhiskerLeft (smallEtaleInclusionDirectImage Y)
      (Functor.sheafPushforwardContinuousComp'
        (smallEtaleInclusion_comp_spacesEtalePullback f) (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X) (spacesEtaleTopology Y))

/-- Restriction then cocontinuous extension along the small étale inclusion is the identity
on spaces-étale sheaves of sets. -/
private def typeInclusionRestrictExtendIso (Z : AlgebraicSpace S) :
    (smallEtaleToSpaces Z).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Z) (spacesEtaleTopology Z) ⋙
      smallEtaleInclusionDirectImage Z ≅
    𝟭 (Sheaf (spacesEtaleTopology Z) (Type (u + 1))) :=
  isoWhiskerRight (typeInclusionRestrictIso Z).symm (smallEtaleInclusionDirectImage Z) ≪≫
    (smallEtalePresentationEquivalence Z).counitIso

/-- Continuous direct images along relocalization and étale base change agree. -/
private def typeRelocalizationPushforwardIso :
    (MorphismProperty.Over.forget (@Etale S) ⊤ Y).sheafPushforwardContinuous
        (Type (u + 1)) (spacesEtaleTopology Y) (overEtaleTopology Y) ⋙
      (etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology Y) ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (overEtaleTopology X) (overEtaleTopology Y) ⋙
        (siteMorphismOfTopoi X).pushforward :=
  Functor.sheafPushforwardContinuousComp (etaleBaseChange f)
      (MorphismProperty.Over.forget (@Etale S) ⊤ Y) (Type (u + 1))
      (smallEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology Y) ≪≫
    Functor.sheafPushforwardContinuousIso (FppfEtale.relocalizationPullbackIso f).symm
      (Type (u + 1)) (smallEtaleTopology X) (overEtaleTopology Y) ≪≫
    (Functor.sheafPushforwardContinuousComp (relocalizationFunctor (𝟙 X)) (Over.pullback f)
      (Type (u + 1)) (smallEtaleTopology X) (overEtaleTopology X)
      (overEtaleTopology Y)).symm

/-- Type-valued pushforward square `π_Y,* ∘ f_small,* ≅ f_big,*_cont ∘ π_X,*`. -/
private def typeSmallBigPushforwardSquareIso :
    (siteMorphismOfTopoi Y).pushforward ⋙ (smallEtaleMorphismOfTopoi f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
        (overEtaleTopology X) (overEtaleTopology Y) ⋙
        (siteMorphismOfTopoi X).pushforward :=
  isoWhiskerLeft (siteMorphismOfTopoi Y).pushforward (typeSmallPushforwardIso f) ≪≫
    isoWhiskerRight (typePiPushforwardIso Y)
      (sheafPushforward (Type (u + 1)) f) ≪≫
    associator
      ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).sheafPushforwardContinuous
        (Type (u + 1)) (spacesEtaleTopology Y) (overEtaleTopology Y))
      ((smallEtaleToSpaces Y).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Y) (spacesEtaleTopology Y))
      (smallEtaleInclusionDirectImage Y ⋙
        (etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
    isoWhiskerLeft
      ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).sheafPushforwardContinuous
        (Type (u + 1)) (spacesEtaleTopology Y) (overEtaleTopology Y))
      ((associator
          ((smallEtaleToSpaces Y).sheafPushforwardContinuous (Type (u + 1))
            (smallEtaleTopology Y) (spacesEtaleTopology Y))
          (smallEtaleInclusionDirectImage Y)
          ((etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
            (smallEtaleTopology X) (spacesEtaleTopology Y))).symm ≪≫
        isoWhiskerRight (typeInclusionRestrictExtendIso Y)
          ((etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
            (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
        leftUnitor
          ((etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
            (smallEtaleTopology X) (spacesEtaleTopology Y))) ≪≫
    typeRelocalizationPushforwardIso f

/-- Inverse-image square `π_X⁻¹ ⋙ f_big⁻¹ ≅ f_small⁻¹ ⋙ π_Y⁻¹` on sheaves of sets. -/
def smallBigInverseImageSquare :
    (siteMorphismOfTopoi X)⁻¹ ⋙ (Big.morphismOfTopoi f)⁻¹ ≅
      (smallEtaleMorphismOfTopoi f)⁻¹ ⋙ (siteMorphismOfTopoi Y)⁻¹ :=
  let adjπX :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      (smallEtaleTopology X) (overEtaleTopology X)
  let adjπY :=
    (relocalizationFunctor (𝟙 Y)).sheafAdjunctionContinuous (Type (u + 1))
      (smallEtaleTopology Y) (overEtaleTopology Y)
  isoWhiskerLeft ((siteMorphismOfTopoi X)⁻¹) (bigInverseImageIsoPullback f) ≪≫
    (conjugateIsoEquiv
        (Adjunction.comp (smallEtaleMorphismOfTopoi f).adjunction adjπY)
        (Adjunction.comp adjπX
          ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
            (overEtaleTopology X) (overEtaleTopology Y)))).symm
      (typeSmallBigPushforwardSquareIso f)

/-- Canonical Type-valued mate `π_X⁻¹ ∘ f_small,* ⟶ f_big,* ∘ π_Y⁻¹`. -/
@[expose] def smallBigPushforwardHom :
    (smallEtaleMorphismOfTopoi f).pushforward ⋙ (siteMorphismOfTopoi X)⁻¹ ⟶
      (siteMorphismOfTopoi Y)⁻¹ ⋙ (Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallEtaleMorphismOfTopoi f).adjunction
    (Big.morphismOfTopoi f).adjunction
    (smallBigInverseImageSquare f)

/-- The small-to-big direct-image comparison is the mate of the inverse-image square. -/
theorem smallBigPushforwardHom_eq :
    smallBigPushforwardHom f =
      DerivedBaseChange.map
        (smallEtaleMorphismOfTopoi f).adjunction
        (Big.morphismOfTopoi f).adjunction
        (smallBigInverseImageSquare f) := rfl

end TypeSheaves

/-- Direct image of abelian sheaves along the big étale morphism of `f`. -/
abbrev bigAbelianPushforward :
    Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (overEtaleTopology Y) (overEtaleTopology X)


end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
