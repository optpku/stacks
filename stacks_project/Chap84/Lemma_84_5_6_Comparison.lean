/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Over.Abelian
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap69.Lemma_69_6_5_Sections
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization
public import stacks_project.Chap84.Lemma_84_5_5_SmallToBig
public import stacks_project.Chap84.Lemma_84_8_4_Big
public import stacks_project.Chap84.Lemma_84_8_4_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small-to-big étale pushforward comparisons of algebraic spaces

Canonical mates identifying small étale direct images with big étale direct images
after `π⁻¹`, at the level of sheaves of sets and of derived categories of abelian
sheaves.
-/

@[expose] public section

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

/-- Forgetting étale from the spaces étale site of `X` to `Over X` is continuous. -/
instance spacesEtaleForget_isContinuous (X : AlgebraicSpace S) :
    (MorphismProperty.Over.forget (@Etale S) ⊤ X).IsContinuous
      (spacesEtaleTopology X) (overEtaleTopology X) :=
  sorry

/-- Relocalization of `𝟙 X` composed with slice pullback along `f` is continuous. -/
instance relocalization_comp_overPullback_isContinuous (f : Y ⟶ X) :
    (relocalizationFunctor (𝟙 X) ⋙ Over.pullback f).IsContinuous
      (smallEtaleTopology X) (overEtaleTopology Y) :=
  Functor.isContinuous_comp (relocalizationFunctor (𝟙 X)) (Over.pullback f)
    (smallEtaleTopology X) (overEtaleTopology X) (overEtaleTopology Y)

/-- Étale base change composed with forgetting étale is continuous. -/
instance etaleBaseChange_comp_forget_isContinuous (f : Y ⟶ X) :
    (etaleBaseChange f ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ Y).IsContinuous
      (smallEtaleTopology X) (overEtaleTopology Y) :=
  Functor.isContinuous_comp (etaleBaseChange f)
    (MorphismProperty.Over.forget (@Etale S) ⊤ Y)
    (smallEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology Y)

/-- Relocalization of `𝟙 Y` followed by postcomposition along `f` is continuous. -/
instance relocalization_comp_overMap_isContinuous (f : Y ⟶ X) :
    (relocalizationFunctor (𝟙 Y) ⋙ Over.map f).IsContinuous
      (smallEtaleTopology Y) (overEtaleTopology X) :=
  Functor.isContinuous_comp (relocalizationFunctor (𝟙 Y)) (Over.map f)
    (smallEtaleTopology Y) (overEtaleTopology Y) (overEtaleTopology X)

variable (f : Y ⟶ X)

/-- Site-level identification of the two paths around the small/big étale square:
étale base change into the spaces site of `Y`, followed by forgetting to `Over Y`,
agrees with relocalization of `𝟙 X` followed by slice pullback along `f`. -/
def smallBigRelocalizationSiteIso :
    etaleBaseChange f ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ Y ≅
      relocalizationFunctor (𝟙 X) ⋙ Over.pullback f :=
  (isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback f)
      (MorphismProperty.Over.forget (@Etale S) ⊤ Y)).symm ≪≫
    associator (smallEtaleInclusion X) (spacesEtalePullback f)
      (MorphismProperty.Over.forget (@Etale S) ⊤ Y) ≪≫
    isoWhiskerLeft (smallEtaleInclusion X)
      (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale S) (Q := ⊤) f) ≪≫
    (associator (smallEtaleInclusion X)
      (MorphismProperty.Over.forget (@Etale S) ⊤ X) (Over.pullback f)).symm ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (smallEtaleInclusion X)
        ((rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ X)).symm ≪≫
          isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X)
            (Over.mapId X).symm)).symm
      (Over.pullback f) ≪≫
    associator (smallEtaleInclusion X)
      (MorphismProperty.Over.forget (@Etale S) ⊤ X ⋙ Over.map (𝟙 X))
      (Over.pullback f)

/-- `smallBigRelocalizationSiteIso` is the composite of
`smallEtaleInclusion_comp_spacesEtalePullback`, `pullbackCompForgetIso`, and identity
reindexing on slices. -/
theorem smallBigRelocalizationSiteIso_eq :
    smallBigRelocalizationSiteIso f =
      (isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback f)
          (MorphismProperty.Over.forget (@Etale S) ⊤ Y)).symm ≪≫
        associator (smallEtaleInclusion X) (spacesEtalePullback f)
          (MorphismProperty.Over.forget (@Etale S) ⊤ Y) ≪≫
        isoWhiskerLeft (smallEtaleInclusion X)
          (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale S) (Q := ⊤) f) ≪≫
        (associator (smallEtaleInclusion X)
          (MorphismProperty.Over.forget (@Etale S) ⊤ X) (Over.pullback f)).symm ≪≫
        isoWhiskerRight
          (isoWhiskerLeft (smallEtaleInclusion X)
            ((rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ X)).symm ≪≫
              isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X)
                (Over.mapId X).symm)).symm
          (Over.pullback f) ≪≫
        associator (smallEtaleInclusion X)
          (MorphismProperty.Over.forget (@Etale S) ⊤ X ⋙ Over.map (𝟙 X))
          (Over.pullback f) :=
  sorry

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
site followed by restriction along `smallEtaleInclusion`. -/
def typePiPushforwardIso (Z : AlgebraicSpace S) :
    (siteMorphismOfTopoi Z).pushforward ≅
      (MorphismProperty.Over.forget (@Etale S) ⊤ Z).sheafPushforwardContinuous
          (Type (u + 1)) (spacesEtaleTopology Z) (overEtaleTopology Z) ⋙
        (smallEtaleInclusion Z).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology Z) (spacesEtaleTopology Z) :=
  isoWhiskerRight
    (Functor.sheafPushforwardContinuousIso
      (isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ Z) (Over.mapId Z) ≪≫
        rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ Z))
      (Type (u + 1)) (spacesEtaleTopology Z) (overEtaleTopology Z))
    ((smallEtaleInclusion Z).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology Z) (spacesEtaleTopology Z))

/-- Restriction along the small étale inclusion is the inverse of cocontinuous extension. -/
def typeInclusionRestrictIso (Z : AlgebraicSpace S) :
    (smallEtaleInclusionDirectImage Z).inv ≅
      (smallEtaleInclusion Z).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Z) (spacesEtaleTopology Z) :=
  Adjunction.leftAdjointUniq
    (smallEtaleInclusionDirectImage Z).asEquivalence.symm.toAdjunction
    ((smallEtaleInclusion Z).sheafAdjunctionCocontinuous (Type (u + 1))
      (smallEtaleTopology Z) (spacesEtaleTopology Z))

/-- Type-valued small étale pushforward agrees with cocontinuous extension followed by
evaluation along étale base change. -/
def typeSmallPushforwardIso :
    (smallEtaleMorphismOfTopoi f).pushforward ≅ sheafPushforward (Type (u + 1)) f :=
  associator (smallEtaleInclusionDirectImage Y)
      ((spacesEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
        (spacesEtaleTopology X) (spacesEtaleTopology Y))
      (smallEtaleInclusionDirectImage X).inv ≪≫
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
def typeInclusionRestrictExtendIso (Z : AlgebraicSpace S) :
    (smallEtaleInclusion Z).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Z) (spacesEtaleTopology Z) ⋙
      smallEtaleInclusionDirectImage Z ≅
    𝟭 (Sheaf (spacesEtaleTopology Z) (Type (u + 1))) :=
  isoWhiskerRight (typeInclusionRestrictIso Z).symm (smallEtaleInclusionDirectImage Z) ≪≫
    (smallEtaleInclusionDirectImage Z).asEquivalence.counitIso

/-- Continuous pushforward along the two paths of `smallBigRelocalizationSiteIso`. -/
def typeRelocalizationPushforwardIso :
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
    Functor.sheafPushforwardContinuousIso (smallBigRelocalizationSiteIso f)
      (Type (u + 1)) (smallEtaleTopology X) (overEtaleTopology Y) ≪≫
    (Functor.sheafPushforwardContinuousComp (relocalizationFunctor (𝟙 X)) (Over.pullback f)
      (Type (u + 1)) (smallEtaleTopology X) (overEtaleTopology X)
      (overEtaleTopology Y)).symm

/-- Type-valued pushforward square `π_Y,* ∘ f_small,* ≅ f_big,*_cont ∘ π_X,*`. -/
def typeSmallBigPushforwardSquareIso :
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
      ((smallEtaleInclusion Y).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Y) (spacesEtaleTopology Y))
      (smallEtaleInclusionDirectImage Y ⋙
        (etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
    isoWhiskerLeft
      ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).sheafPushforwardContinuous
        (Type (u + 1)) (spacesEtaleTopology Y) (overEtaleTopology Y))
      ((associator
          ((smallEtaleInclusion Y).sheafPushforwardContinuous (Type (u + 1))
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
def smallBigPushforwardHom :
    (smallEtaleMorphismOfTopoi f).pushforward ⋙ (siteMorphismOfTopoi X)⁻¹ ⟶
      (siteMorphismOfTopoi Y)⁻¹ ⋙ (Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallEtaleMorphismOfTopoi f).adjunction
    (Big.morphismOfTopoi f).adjunction
    (smallBigInverseImageSquare f)

/-- `smallBigPushforwardHom` is the right mate of the inverse-image square. -/
theorem smallBigPushforwardHom_eq :
    smallBigPushforwardHom f =
      DerivedBaseChange.map
        (smallEtaleMorphismOfTopoi f).adjunction
        (Big.morphismOfTopoi f).adjunction
        (smallBigInverseImageSquare f) :=
  sorry

end TypeSheaves

section AbelianSheaves

variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
variable [∀ P : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (relocalizationFunctor (𝟙 Y)).op.HasLeftKanExtension P]
variable [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Over.map f).op.HasPointwiseRightKanExtension P]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]

/-- Direct image of abelian sheaves along the big étale morphism of `f`. -/
abbrev bigAbelianPushforward :
    Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Inverse image of abelian sheaves along the big étale morphism of `f`. -/
abbrev bigAbelianInverseImage :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f

/-- Big étale abelian pushforward is additive. -/
instance bigAbelianPushforward_additive : (bigAbelianPushforward f).Additive := sorry

/-- Direct image along `π_X` identifies with restriction from `Over X` to the spaces étale
site followed by restriction along `smallEtaleInclusion`. -/
def etalePiPushforwardIso (Z : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 Z)).op.HasLeftKanExtension P] :
    etalePiPushforward Z ≅
      (MorphismProperty.Over.forget (@Etale S) ⊤ Z).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (spacesEtaleTopology Z) (overEtaleTopology Z) ⋙
        (smallEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Z) (spacesEtaleTopology Z) :=
  isoWhiskerRight
    (Functor.sheafPushforwardContinuousIso
      (isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ Z) (Over.mapId Z) ≪≫
        rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ Z))
      AddCommGrpCat.{u + 1} (spacesEtaleTopology Z) (overEtaleTopology Z))
    ((smallEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Z) (spacesEtaleTopology Z))

/-- Restricting an abelian sheaf on `Z_spaces,étale` to `Z_étale` and extending it back
is isomorphic to the identity. -/
def inclusionRestrictExtendIso (Z : AlgebraicSpace S)
    [(smallEtaleInclusion Z).IsCoverDense (spacesEtaleTopology Z)] :
    (smallEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology Z) (spacesEtaleTopology Z) ⋙
      (smallEtaleInclusion Z).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology Z) (spacesEtaleTopology Z) ≅
    𝟭 (Sheaf (spacesEtaleTopology Z) AddCommGrpCat.{u + 1}) :=
  let restrict :=
    (smallEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  let extend :=
    (smallEtaleInclusion Z).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  let adj :=
    (smallEtaleInclusion Z).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  NatIso.ofComponents
    (fun F ↦
      let i :
          (smallEtaleInclusion Z).op ⋙ ((restrict ⋙ extend).obj F).obj ≅
            (smallEtaleInclusion Z).op ⋙ F.obj :=
        { hom := (adj.counit.app (restrict.obj F)).hom
          inv := (restrict.map (adj.unit.app F)).hom
          hom_inv_id := sorry
          inv_hom_id := sorry }
      (fullyFaithfulSheafToPresheaf (spacesEtaleTopology Z) AddCommGrpCat.{u + 1}).preimageIso
        { hom := Functor.IsCoverDense.sheafHom i.hom
          inv := Functor.IsCoverDense.sheafHom i.inv
          hom_inv_id := sorry
          inv_hom_id := sorry })
    sorry

/-- Inverse-image square `π_X⁻¹ ⋙ f_big⁻¹ ≅ f_small⁻¹ ⋙ π_Y⁻¹` on abelian sheaves. -/
def abelianSmallBigInverseImageSquare :
    etalePiInverseImage X ⋙ bigAbelianInverseImage f ≅
      sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ etalePiInverseImage Y :=
  (conjugateIsoEquiv
      (Adjunction.comp (sheafInverseImageAdjunction f) (etalePiAdjunction Y))
      (Adjunction.comp (etalePiAdjunction X)
        (etaleTopology.overMapPushforwardAdjunction AddCommGrpCat.{u + 1} f))).symm
    (associator (etalePiPushforward Y)
        ((smallEtaleInclusion Y).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology Y))
        ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
      isoWhiskerRight (etalePiPushforwardIso Y)
        ((smallEtaleInclusion Y).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
          (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
      associator
        ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (spacesEtaleTopology Y) (overEtaleTopology Y))
        ((smallEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology Y))
        ((smallEtaleInclusion Y).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
          (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
      isoWhiskerLeft
        ((MorphismProperty.Over.forget (@Etale S) ⊤ Y).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (spacesEtaleTopology Y) (overEtaleTopology Y))
        ((associator
            ((smallEtaleInclusion Y).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (smallEtaleTopology Y) (spacesEtaleTopology Y))
            ((smallEtaleInclusion Y).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
              (smallEtaleTopology Y) (spacesEtaleTopology Y))
            ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (smallEtaleTopology X) (spacesEtaleTopology Y))).symm ≪≫
          isoWhiskerRight (inclusionRestrictExtendIso Y)
            ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (smallEtaleTopology X) (spacesEtaleTopology Y)) ≪≫
          leftUnitor
            ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (smallEtaleTopology X) (spacesEtaleTopology Y))) ≪≫
      Functor.sheafPushforwardContinuousIso (smallBigRelocalizationSiteIso f)
        AddCommGrpCat.{u + 1} (smallEtaleTopology X) (overEtaleTopology Y))

section AbelianDerived

variable [PreservesFiniteLimits
    ((relocalizationFunctor (𝟙 X)).op.lan :
      ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
variable [PreservesFiniteLimits
    ((relocalizationFunctor (𝟙 Y)).op.lan :
      ((smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian f).Additive]
variable [(bigAbelianPushforward f).Additive]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `plusSmallBigPushforwardHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Small étale abelian pushforward is additive. -/
instance sheafPushforwardAbelian_additive : (sheafPushforwardAbelian f).Additive := sorry

/-- Big étale abelian pushforward remains additive after the Preadditive pin. -/
instance bigAbelianPushforward_additive_preadditive :
    (bigAbelianPushforward f).Additive := sorry

/-- Exact inverse image `π⁻¹` on abelian small-étale sheaves. -/
abbrev etalePiExact (Z : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 Z)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 Z)).op.lan :
        ((smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          ((Over Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))] :
    Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (overEtaleTopology Z) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (etalePiInverseImage Z)

/-- Exact inverse image along the big étale morphism of `f`. -/
abbrev bigEtaleExact :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (bigAbelianInverseImage f)

/-- Exact inverse image `f_small⁻¹` on abelian small-étale sheaves. -/
abbrev smallEtaleExact :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (sheafInverseImage AddCommGrpCat.{u + 1} f)

/-- Bundled exact-functor form of the abelian inverse-image square. -/
def abelianSmallBigExactSquare :
    (etalePiExact X).comp (bigEtaleExact f) ≅
      (smallEtaleExact f).comp (etalePiExact Y) :=
  (exactFunctor
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})).isoMk
    (abelianSmallBigInverseImageSquare f)

/-- Bounded-below derived inverse image `π⁻¹` on `D⁺`. -/
abbrev plusPiInverseImage (Z : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (overEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (overEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 Z)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 Z)).op.lan :
        ((smallEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          ((Over Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))] :
    DerivedCategory.Plus (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (overEtaleTopology Z) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (etalePiExact Z)

/-- Inverse-image square on `D⁺` induced by the abelian small/big square. -/
def plusSmallBigInverseImageSquare :
    plusPiInverseImage X ⋙ ExactFunctor.Derived.Plus.functor (bigEtaleExact f) ≅
      ExactFunctor.Derived.Plus.functor (smallEtaleExact f) ⋙ plusPiInverseImage Y :=
  ExactFunctor.Derived.Plus.squareIso
    (etalePiExact X) (bigEtaleExact f) (smallEtaleExact f) (etalePiExact Y)
    (abelianSmallBigExactSquare f)

variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}))]
variable [(bigAbelianPushforward f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1}))]

/-- Canonical `D⁺` mate `π_X⁻¹ Rf_small,* ⟶ Rf_big,* π_Y⁻¹`. -/
def plusSmallBigPushforwardHom :
    Adjunction.Derived.Plus.right (sheafPushforwardAbelian f) ⋙ plusPiInverseImage X ⟶
      plusPiInverseImage Y ⋙
        Adjunction.Derived.Plus.right (bigAbelianPushforward f) :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (smallEtaleExact f)
      (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
    (Adjunction.Derived.Plus.adjunction (bigEtaleExact f)
      (bigAbelianPushforward f)
      (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
    (plusSmallBigInverseImageSquare f)

/-- `plusSmallBigPushforwardHom` is the right mate of the `D⁺` inverse-image square. -/
theorem plusSmallBigPushforwardHom_eq :
    plusSmallBigPushforwardHom f =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (smallEtaleExact f)
          (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
        (Adjunction.Derived.Plus.adjunction (bigEtaleExact f)
          (bigAbelianPushforward f)
          (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
        (plusSmallBigInverseImageSquare f) :=
  sorry

section UnboundedDerived

variable [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]

/-- Inverse-image square on unbounded derived categories. -/
def unboundedSmallBigInverseImageSquare :
    (etalePiExact X).mapDerivedCategory ⋙ (bigEtaleExact f).mapDerivedCategory ≅
      (smallEtaleExact f).mapDerivedCategory ⋙ (etalePiExact Y).mapDerivedCategory :=
  ExactFunctor.MapDerivedCategory.squareIso
    (etalePiExact X) (bigEtaleExact f) (smallEtaleExact f) (etalePiExact Y)
    (abelianSmallBigExactSquare f)

/-- Canonical unbounded derived mate `π_X⁻¹ Rf_small,* ⟶ Rf_big,* π_Y⁻¹`. -/
def unboundedSmallBigPushforwardHom :
    Adjunction.Derived.KInjective.right (sheafPushforwardAbelian f) ⋙
        (etalePiExact X).mapDerivedCategory ⟶
      (etalePiExact Y).mapDerivedCategory ⋙
        Adjunction.Derived.KInjective.right (bigAbelianPushforward f) :=
  DerivedBaseChange.map
    (Adjunction.Derived.KInjective.adjunction (smallEtaleExact f)
      (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
    (Adjunction.Derived.KInjective.adjunction (bigEtaleExact f)
      (bigAbelianPushforward f)
      (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
    (unboundedSmallBigInverseImageSquare f)

/-- `unboundedSmallBigPushforwardHom` is the right mate of the unbounded inverse-image square. -/
theorem unboundedSmallBigPushforwardHom_eq :
    unboundedSmallBigPushforwardHom f =
      DerivedBaseChange.map
        (Adjunction.Derived.KInjective.adjunction (smallEtaleExact f)
          (sheafPushforwardAbelian f) (sheafInverseImageAdjunction f))
        (Adjunction.Derived.KInjective.adjunction (bigEtaleExact f)
          (bigAbelianPushforward f)
          (etaleTopology.overMapCocontinuousAdjunction AddCommGrpCat.{u + 1} f))
        (unboundedSmallBigInverseImageSquare f) :=
  sorry

end UnboundedDerived

end AbelianDerived

end AbelianSheaves

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
