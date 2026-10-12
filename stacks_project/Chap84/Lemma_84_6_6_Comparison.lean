/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap84.Lemma_84_6_6_InverseImage

/-!
# Canonical fppf/étale derived base change of algebraic spaces

This leaf owns the inverse-image square identifying `a_Y⁻¹ ⋙ f_big,fppf⁻¹` with
`f_small⁻¹ ⋙ a_X⁻¹` on `D⁺`, and the canonical mate
`R f_small,* ⋙ a_Y⁻¹ ⟶ a_X⁻¹ ⋙ R f_big,fppf,*`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.Limits CategoryTheory.Adjunction
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor (associator isoWhiskerLeft isoWhiskerRight whiskerLeft whiskerRight)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

variable {S : Scheme.{u}}

/-- Forgetting étale from the spaces étale site of `X` to `Over X` is continuous. -/
instance spacesEtaleForget_isContinuous (X : AlgebraicSpace S) :
    (MorphismProperty.Over.forget (@Etale S) ⊤ X).IsContinuous
      (spacesEtaleTopology X) (overEtaleTopology X) := sorry

/-- Relocalization of `𝟙 Y` composed with slice pullback along `f` is continuous. -/
instance relocalization_comp_overPullback_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f).IsContinuous
      (smallEtaleTopology Y) (overEtaleTopology X) :=
  Functor.isContinuous_comp (relocalizationFunctor (𝟙 Y)) (Over.pullback f)
    (smallEtaleTopology Y) (overEtaleTopology Y) (overEtaleTopology X)

/-- Étale base change composed with forgetting étale is continuous. -/
instance etaleBaseChange_comp_forget_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (etaleBaseChange f ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ X).IsContinuous
      (smallEtaleTopology Y) (overEtaleTopology X) :=
  Functor.isContinuous_comp (etaleBaseChange f)
    (MorphismProperty.Over.forget (@Etale S) ⊤ X)
    (smallEtaleTopology Y) (spacesEtaleTopology X) (overEtaleTopology X)

/-- Relocalization of `𝟙 Y` followed by slice pullback along `f` identifies with étale
base change followed by forgetting étale. -/
def relocalizationPullbackIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f ≅
      etaleBaseChange f ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ X :=
  associator (smallEtaleInclusion Y)
      (MorphismProperty.Over.forget (@Etale S) ⊤ Y ⋙ Over.map (𝟙 Y))
      (Over.pullback f) ≪≫
    isoWhiskerLeft (smallEtaleInclusion Y)
      (associator (MorphismProperty.Over.forget (@Etale S) ⊤ Y) (Over.map (𝟙 Y))
          (Over.pullback f) ≪≫
        isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ Y)
          (isoWhiskerRight (Over.mapId Y) (Over.pullback f) ≪≫
            Functor.leftUnitor (Over.pullback f))) ≪≫
    (associator (smallEtaleInclusion Y) (spacesEtalePullback f)
        (MorphismProperty.Over.forget (@Etale S) ⊤ X)).symm ≪≫
    isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback f)
      (MorphismProperty.Over.forget (@Etale S) ⊤ X)

/-- `relocalizationPullbackIso` is the composite of `Over.mapId`, the definitional
forget/pullback identification, and `smallEtaleInclusion_comp_spacesEtalePullback`. -/
theorem relocalizationPullbackIso_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    relocalizationPullbackIso f =
      associator (smallEtaleInclusion Y)
          (MorphismProperty.Over.forget (@Etale S) ⊤ Y ⋙ Over.map (𝟙 Y))
          (Over.pullback f) ≪≫
        isoWhiskerLeft (smallEtaleInclusion Y)
          (associator (MorphismProperty.Over.forget (@Etale S) ⊤ Y) (Over.map (𝟙 Y))
              (Over.pullback f) ≪≫
            isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ Y)
              (isoWhiskerRight (Over.mapId Y) (Over.pullback f) ≪≫
                Functor.leftUnitor (Over.pullback f))) ≪≫
        (associator (smallEtaleInclusion Y) (spacesEtalePullback f)
            (MorphismProperty.Over.forget (@Etale S) ⊤ X)).symm ≪≫
        isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback f)
          (MorphismProperty.Over.forget (@Etale S) ⊤ X) := sorry

/-- Direct image along `π_X` identifies with restriction from `Over X` to the spaces étale
site followed by restriction along `smallEtaleInclusion`. -/
def etalePiPushforwardIso (X : AlgebraicSpace S) :
    etalePiPushforward X ≅
      (MorphismProperty.Over.forget (@Etale S) ⊤ X).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (spacesEtaleTopology X) (overEtaleTopology X) ⋙
        (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology X) :=
  isoWhiskerRight
    (Functor.sheafPushforwardContinuousIso
      (isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X) (Over.mapId X) ≪≫
        Functor.rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ X))
      AddCommGrpCat.{u + 1} (spacesEtaleTopology X) (overEtaleTopology X))
    ((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- `etalePiPushforwardIso` drops `Over.map (𝟙 X)` after the forgetful functor. -/
theorem etalePiPushforwardIso_eq (X : AlgebraicSpace S) :
    etalePiPushforwardIso X =
      isoWhiskerRight
        (Functor.sheafPushforwardContinuousIso
          (isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X) (Over.mapId X) ≪≫
            Functor.rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ X))
          AddCommGrpCat.{u + 1} (spacesEtaleTopology X) (overEtaleTopology X))
        ((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology X)) := sorry

/-- The small étale inclusion is cover-dense in the spaces étale topology. -/
instance smallEtaleInclusion_isCoverDense (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X) := sorry

/-- Restricting an abelian sheaf on `X_spaces,étale` to `X_étale` and extending it back
is isomorphic to the identity. The forward and reverse maps are the cover-dense
extensions of the adjunction counit and of restriction of the unit. -/
def inclusionRestrictExtendIso (X : AlgebraicSpace S) :
    (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
      (smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X) ≅
    𝟭 (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  let restrict :=
    (smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let extend :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let adj :=
    (smallEtaleInclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X)
  NatIso.ofComponents
    (fun F ↦
      let i :
          (smallEtaleInclusion X).op ⋙ ((restrict ⋙ extend).obj F).obj ≅
            (smallEtaleInclusion X).op ⋙ F.obj :=
        { hom := (adj.counit.app (restrict.obj F)).hom
          inv := (restrict.map (adj.unit.app F)).hom
          hom_inv_id := sorry
          inv_hom_id := sorry }
      (fullyFaithfulSheafToPresheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).preimageIso
        { hom := Functor.IsCoverDense.sheafHom i.hom
          inv := Functor.IsCoverDense.sheafHom i.inv
          hom_inv_id := sorry
          inv_hom_id := sorry })
    sorry

/-- Restricting `inclusionRestrictExtendIso` to the small étale site recovers the
adjunction counit. -/
theorem inclusionRestrictExtendIso_restrict (X : AlgebraicSpace S)
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology X)).map
        ((inclusionRestrictExtendIso X).hom.app F) =
      ((smallEtaleInclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app
        (((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology X)).obj F) := sorry

/-- The direct-image identification `π_{X,*} ⋙ f_small,* ≅ f_big,étale,* ⋙ π_{Y,*}`
induced by `relocalizationPullbackIso`, `etalePiPushforwardIso`, and
`inclusionRestrictExtendIso`. -/
def piPushforwardSquareIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etalePiPushforward X ⋙ sheafPushforward AddCommGrpCat.{u + 1} f ≅
      etaleTopology.overMapPushforward AddCommGrpCat.{u + 1} f ⋙ etalePiPushforward Y :=
  associator (etalePiPushforward X)
      ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X))
      ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
    isoWhiskerRight (etalePiPushforwardIso X)
      ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
    associator
      ((MorphismProperty.Over.forget (@Etale S) ⊤ X).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (spacesEtaleTopology X) (overEtaleTopology X))
      ((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X))
      ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
    isoWhiskerLeft
      ((MorphismProperty.Over.forget (@Etale S) ⊤ X).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (spacesEtaleTopology X) (overEtaleTopology X))
      ((associator
          ((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology X))
          ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology X))
          ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology Y) (spacesEtaleTopology X))).symm ≪≫
        isoWhiskerRight (inclusionRestrictExtendIso X)
          ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
        Functor.leftUnitor
          ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology Y) (spacesEtaleTopology X))) ≪≫
    Functor.sheafPushforwardContinuousIso (relocalizationPullbackIso f).symm
      AddCommGrpCat.{u + 1} (smallEtaleTopology Y) (overEtaleTopology X)

/-- `piPushforwardSquareIso` is the composite of `etalePiPushforwardIso`,
`inclusionRestrictExtendIso`, and sheaf pushforward of `relocalizationPullbackIso`. -/
theorem piPushforwardSquareIso_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    piPushforwardSquareIso f =
      associator (etalePiPushforward X)
          ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology X))
          ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
        isoWhiskerRight (etalePiPushforwardIso X)
          ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
            (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
        associator
          ((MorphismProperty.Over.forget (@Etale S) ⊤ X).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1} (spacesEtaleTopology X) (overEtaleTopology X))
          ((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology X))
          ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
            (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
            (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
        isoWhiskerLeft
          ((MorphismProperty.Over.forget (@Etale S) ⊤ X).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1} (spacesEtaleTopology X) (overEtaleTopology X))
          ((associator
              ((smallEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                (smallEtaleTopology X) (spacesEtaleTopology X))
              ((smallEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
                (smallEtaleTopology X) (spacesEtaleTopology X))
              ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                (smallEtaleTopology Y) (spacesEtaleTopology X))).symm ≪≫
            isoWhiskerRight (inclusionRestrictExtendIso X)
              ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                (smallEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
            Functor.leftUnitor
              ((etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                (smallEtaleTopology Y) (spacesEtaleTopology X))) ≪≫
        Functor.sheafPushforwardContinuousIso (relocalizationPullbackIso f).symm
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y) (overEtaleTopology X) := sorry

/-- The sheaf-level inverse-image square `π_Y⁻¹ ⋙ f_big,étale⁻¹ ≅ f_small⁻¹ ⋙ π_X⁻¹`,
conjugate to `piPushforwardSquareIso` along the small-pushforward and slice-pushforward
adjunctions. -/
def piInverseImageSquareIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etalePiInverseImage Y ⋙ etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f ≅
      sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ etalePiInverseImage X :=
  (conjugateIsoEquiv
      (Adjunction.comp (sheafPushforwardAdjunction f) (etalePiAdjunction X))
      (Adjunction.comp (etalePiAdjunction Y)
        (etaleTopology.overMapPushforwardAdjunction AddCommGrpCat.{u + 1} f))).symm
    (piPushforwardSquareIso f)

/-- `piInverseImageSquareIso` is the conjugate of `piPushforwardSquareIso`. -/
theorem piInverseImageSquareIso_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    piInverseImageSquareIso f =
      (conjugateIsoEquiv
          (Adjunction.comp (sheafPushforwardAdjunction f) (etalePiAdjunction X))
          (Adjunction.comp (etalePiAdjunction Y)
            (etaleTopology.overMapPushforwardAdjunction AddCommGrpCat.{u + 1} f))).symm
        (piPushforwardSquareIso f) := sorry

/-- The sheaf-level inverse-image comparison
`π_Y⁻¹ ⋙ f_big,étale⁻¹ ⟶ f_small⁻¹ ⋙ π_X⁻¹`. -/
abbrev piInverseImageSquare {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etalePiInverseImage Y ⋙ etaleTopology.overMapPullback AddCommGrpCat.{u + 1} f ⟶
      sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ etalePiInverseImage X :=
  (piInverseImageSquareIso f).hom

/-- `piInverseImageSquare` is the forward map of `piInverseImageSquareIso`. -/
theorem piInverseImageSquare_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    piInverseImageSquare f = (piInverseImageSquareIso f).hom := sorry

/-- The sheaf-level inverse-image square is an isomorphism. -/
theorem piInverseImageSquareIso_spec {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsIso (piInverseImageSquareIso f).hom := sorry

/-- The bounded-below inverse-image square
`π_Y⁻¹ ⋙ f_big,étale⁻¹ ≅ f_small⁻¹ ⋙ π_X⁻¹` on `D⁺`. -/
def piDerivedSquareIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    piInverseImagePlus Y ⋙ Derived.Over.Plus.pullback etaleTopology f ≅
      smallInverseImagePlus f ⋙ piInverseImagePlus X :=
  ExactFunctor.Derived.Plus.squareIso
    (etalePiExact Y) (etaleTopology.overMapPullbackExact f)
    (smallInverseExact f) (etalePiExact X)
    ((exactFunctor _ _).isoMk (piInverseImageSquareIso f))

/-- The bounded-below inverse-image square
`a_Y⁻¹ ⋙ f_big,fppf⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on `D⁺`. -/
def inverseImageSquareIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    aInverseAbPlus Y ⋙ Derived.Over.Plus.pullback (fppfTopology S) f ≅
      smallInverseImagePlus f ⋙ aInverseAbPlus X :=
  associator (piInverseImagePlus Y) (Derived.Plus.pullback etale_le_fppf Y)
      (Derived.Over.Plus.pullback (fppfTopology S) f) ≪≫
    isoWhiskerLeft (piInverseImagePlus Y)
      (Derived.Plus.overMapPullbackComparisonIso etale_le_fppf f).symm ≪≫
    (associator (piInverseImagePlus Y) (Derived.Over.Plus.pullback etaleTopology f)
      (Derived.Plus.pullback etale_le_fppf X)).symm ≪≫
    isoWhiskerRight (piDerivedSquareIso f) (Derived.Plus.pullback etale_le_fppf X) ≪≫
    associator (smallInverseImagePlus f) (piInverseImagePlus X)
      (Derived.Plus.pullback etale_le_fppf X)

/-- The canonical derived base-change transformation
`R f_small,* ⋙ a_Y⁻¹ ⟶ a_X⁻¹ ⋙ R f_big,fppf,*`. -/
def derivedBaseChange {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Adjunction.Derived.Plus.right (sheafPushforward AddCommGrpCat.{u + 1} f) ⋙
        aInverseAbPlus Y ⟶
      aInverseAbPlus X ⋙ Derived.Over.Plus.pushforward (fppfTopology S) f :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (smallInverseExact f)
      (sheafPushforward AddCommGrpCat.{u + 1} f) (sheafPushforwardAdjunction f))
    (Derived.Over.Plus.adjunction (fppfTopology S) f) (inverseImageSquareIso f)

/-- `derivedBaseChange` is the mate of `inverseImageSquareIso`. -/
theorem derivedBaseChange_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    derivedBaseChange f =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (smallInverseExact f)
          (sheafPushforward AddCommGrpCat.{u + 1} f) (sheafPushforwardAdjunction f))
        (Derived.Over.Plus.adjunction (fppfTopology S) f) (inverseImageSquareIso f) := sorry

/-- The component of canonical derived base change at `K ∈ D⁺(X_étale)`. -/
abbrev derivedBaseChangeApp {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (aInverseAbPlus Y).obj
        ((Adjunction.Derived.Plus.right (sheafPushforward AddCommGrpCat.{u + 1} f)).obj K) ⟶
      (Derived.Over.Plus.pushforward (fppfTopology S) f).obj ((aInverseAbPlus X).obj K) :=
  (derivedBaseChange f).app K

/-- `derivedBaseChangeApp` is the component of `derivedBaseChange`. -/
theorem derivedBaseChangeApp_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    derivedBaseChangeApp f K = (derivedBaseChange f).app K := sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
