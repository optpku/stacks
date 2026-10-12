/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_11
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap84.«84_5_2_1_Site»

/-!
# Big versus small étale direct images of algebraic spaces

Restriction of the big étale direct image along `f : Y ⟶ X` is canonically
isomorphic to the small étale direct image of the restricted sheaf. The
identification is induced by the commuting square of sites
`smallEtaleToBig X ⋙ Over.pullback f ≅ etaleBaseChange f ⋙ spacesEtaleToBig Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}}

/-- Direct image of type-valued sheaves on big étale slice sites along `f : Y ⟶ X`. -/
abbrev bigPushforward {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  bigEtaleTopology.overMapPushforward (Type (u + 1)) f

/-- `bigPushforward f` is slice-site direct image along `Over.pullback f`. -/
theorem bigPushforward_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    bigPushforward f = bigEtaleTopology.overMapPushforward (Type (u + 1)) f :=
  rfl

/-- Direct image of abelian sheaves on big étale slice sites along `f : Y ⟶ X`. -/
abbrev bigPushforwardAbelian {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  bigEtaleTopology.overMapPushforward AddCommGrpCat.{u + 1} f

/-- `bigPushforwardAbelian f` is slice-site direct image of abelian sheaves. -/
theorem bigPushforwardAbelian_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    bigPushforwardAbelian f =
      bigEtaleTopology.overMapPushforward AddCommGrpCat.{u + 1} f :=
  rfl

/-- The composite `smallEtaleToBig X ⋙ Over.pullback f` is continuous. -/
instance smallEtaleToBig_comp_overPullback_isContinuous {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    (smallEtaleToBig X ⋙ Over.pullback f).IsContinuous
      (smallEtaleTopology X) (overEtaleTopology Y) :=
  Functor.isContinuous_comp (smallEtaleToBig X) (Over.pullback f)
    (smallEtaleTopology X) (overEtaleTopology X) (overEtaleTopology Y)

/-- The composite `etaleBaseChange f ⋙ spacesEtaleToBig Y` is continuous. -/
instance etaleBaseChange_comp_spacesEtaleToBig_isContinuous {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    (etaleBaseChange f ⋙ spacesEtaleToBig Y).IsContinuous
      (smallEtaleTopology X) (overEtaleTopology Y) :=
  Functor.isContinuous_comp (etaleBaseChange f) (spacesEtaleToBig Y)
    (smallEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology Y)

/-- Site-level commuting square: inclusion into `(Spaces/X)_étale` followed by
base change along `f` agrees with small étale base change into `(Spaces/Y)_étale`. -/
def pullbackRelocalizationIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    smallEtaleToBig X ⋙ Over.pullback f ≅
      etaleBaseChange f ⋙ spacesEtaleToBig Y :=
  Functor.associator (smallEtaleInclusion X) (spacesEtaleToBig X) (Over.pullback f) ≪≫
    Functor.isoWhiskerLeft (smallEtaleInclusion X)
      (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale S) (Q := ⊤) f).symm ≪≫
    (Functor.associator (smallEtaleInclusion X) (spacesEtalePullback f)
        (spacesEtaleToBig Y)).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback f)
      (spacesEtaleToBig Y)

/-- A sheaf on `X_spaces,étale` is the extension of its restriction to `X_étale`.
Both the forward and inverse maps are composites of the Lemma 66.18.3 equivalence
with the unique-left-adjoint comparison to continuous restriction. -/
def restrictionExtensionIso (X : AlgebraicSpace S) :
    𝟭 (Sheaf (spacesEtaleTopology X) (Type (u + 1))) ≅
      (smallEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        smallEtaleInclusionDirectImage X :=
  (smallEtaleInclusionDirectImage X).asEquivalence.counitIso.symm ≪≫
    Functor.isoWhiskerRight
      (smallEtaleInclusionDirectImage_inv_sheafPushforwardContinuous X)
      (smallEtaleInclusionDirectImage X)

/-- Small étale pushforward of a restricted sheaf is continuous pushforward along
`etaleBaseChange f ⋙ spacesEtaleToBig Y`. -/
def restrictThenSmallPushforwardIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    restrictToSmallEtale Y ⋙ sheafPushforwardType f ≅
      (etaleBaseChange f ⋙ spacesEtaleToBig Y).sheafPushforwardContinuous
        (Type (u + 1)) (smallEtaleTopology X) (overEtaleTopology Y) :=
  Functor.isoWhiskerLeft ((spacesEtaleToBig Y).sheafPushforwardContinuous (Type (u + 1))
      (spacesEtaleTopology Y) (overEtaleTopology Y))
    (Functor.isoWhiskerRight (restrictionExtensionIso Y).symm
      ((etaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology Y)))

/-- Restriction of the big étale direct image is naturally isomorphic to the small
étale direct image of the restriction. -/
def pushforwardRestrictIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    bigPushforward f ⋙ restrictToSmallEtale X ≅
      restrictToSmallEtale Y ⋙ sheafPushforwardType f :=
  Functor.sheafPushforwardContinuousComp' (pullbackRelocalizationIso f) (Type (u + 1))
      (smallEtaleTopology X) (overEtaleTopology X) (overEtaleTopology Y) ≪≫
    (restrictThenSmallPushforwardIso f).symm

/-- Restriction of the big étale abelian direct image is naturally isomorphic to
continuous pushforward along the small étale base-change presentation of the
site square. -/
def pushforwardRestrictIsoAbelian {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    bigPushforwardAbelian f ⋙ restrictToSmallEtaleAbelian X ≅
      (etaleBaseChange f ⋙ spacesEtaleToBig Y).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (smallEtaleTopology X) (overEtaleTopology Y) :=
  Functor.sheafPushforwardContinuousComp' (pullbackRelocalizationIso f)
      AddCommGrpCat.{u + 1} (smallEtaleTopology X) (overEtaleTopology X)
      (overEtaleTopology Y)

/-- The restriction of a big étale direct image is canonically isomorphic to the
small étale direct image of the restricted sheaf. -/
def bigToSmallPushforwardIso {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) :
    (restrictToSmallEtale X).obj ((bigPushforward f).obj F) ≅
      (sheafPushforwardType f).obj ((restrictToSmallEtale Y).obj F) :=
  (pushforwardRestrictIso f).app F

/-- The component of `pushforwardRestrictIso` at `F` is `bigToSmallPushforwardIso`. -/
theorem pushforwardRestrictIso_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) :
    (pushforwardRestrictIso f).app F = bigToSmallPushforwardIso f F :=
  rfl

/-- The restriction of a big étale abelian direct image is canonically isomorphic
to continuous pushforward along `etaleBaseChange f ⋙ spacesEtaleToBig Y`. -/
def bigToSmallPushforwardIso_abelian {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (restrictToSmallEtaleAbelian X).obj ((bigPushforwardAbelian f).obj F) ≅
      ((etaleBaseChange f ⋙ spacesEtaleToBig Y).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (smallEtaleTopology X) (overEtaleTopology Y)).obj F :=
  (pushforwardRestrictIsoAbelian f).app F

/-- The component of `pushforwardRestrictIsoAbelian` at `F` is
`bigToSmallPushforwardIso_abelian`. -/
theorem pushforwardRestrictIsoAbelian_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (pushforwardRestrictIsoAbelian f).app F = bigToSmallPushforwardIso_abelian f F :=
  rfl

/-- The fibre product object of the left-hand site functor is the pullback
projection `U ×_X Y ⟶ Y`. -/
theorem bigToSmallPushforwardIso_obj_pullback {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (U : smallEtaleSite X) :
    ((smallEtaleToBig X ⋙ Over.pullback f).obj U).hom =
      pullback.snd ((smallEtaleToBig X).obj U).hom f :=
  rfl

/-- The ring sheaves obtained by restricting `R` along the two presentations of
the site square are canonically isomorphic. -/
def restrictedRingIso {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (R : Sheaf (overEtaleTopology Y) RingCat.{u}) :
    ((smallEtaleToBig X ⋙ Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology X) (overEtaleTopology Y)).obj R ≅
      ((etaleBaseChange f ⋙ spacesEtaleToBig Y).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology X) (overEtaleTopology Y)).obj R :=
  (Functor.sheafPushforwardContinuousIso (pullbackRelocalizationIso f) RingCat.{u}
    (smallEtaleTopology X) (overEtaleTopology Y)).app R

/-- `restrictedRingIso` is the component of `sheafPushforwardContinuousIso` of
`pullbackRelocalizationIso`. -/
theorem restrictedRingIso_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (R : Sheaf (overEtaleTopology Y) RingCat.{u}) :
    restrictedRingIso f R =
      (Functor.sheafPushforwardContinuousIso (pullbackRelocalizationIso f) RingCat.{u}
        (smallEtaleTopology X) (overEtaleTopology Y)).app R :=
  rfl

/-- Module pushforward of an `R`-module along `smallEtaleToBig X ⋙ Over.pullback f`. -/
abbrev modulePushforwardAlongComposite {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (R : Sheaf (overEtaleTopology Y) RingCat.{u}) :
    SheafOfModules.{u} R ⥤
      SheafOfModules.{u}
        (((smallEtaleToBig X ⋙ Over.pullback f).sheafPushforwardContinuous RingCat.{u}
            (smallEtaleTopology X) (overEtaleTopology Y)).obj R) :=
  SheafOfModules.pushforward (𝟙 _)

/-- `modulePushforwardAlongComposite` is pushforward along the identity ring map. -/
theorem modulePushforwardAlongComposite_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (R : Sheaf (overEtaleTopology Y) RingCat.{u}) :
    modulePushforwardAlongComposite f R = SheafOfModules.pushforward (𝟙 _) :=
  rfl

/-- Natural isomorphism of module pushforwards induced by the site square
`pullbackRelocalizationIso`. This is the `𝒪`-module form of the identification:
the two site-functor presentations of `U ×_X Y` induce isomorphic module
pushforwards over the isomorphic restricted ring sheaves. It does not identify
those objects with `Modules.pushforward f` on `Y.Modules`. -/
def bigToSmallPushforwardIso_modulesNatIso {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (R : Sheaf (overEtaleTopology Y) RingCat.{u}) :
    modulePushforwardAlongComposite f R ≅
      SheafOfModules.pushforward (restrictedRingIso f R).hom :=
  SheafOfModules.pushforwardNatIso (𝟙 _) (pullbackRelocalizationIso f).symm

/-- If `F` is a sheaf of modules on the big étale site of `Y`, the two
presentations of the site square yield canonically isomorphic module
pushforwards on `X_étale`. -/
def bigToSmallPushforwardIso_modules {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (R : Sheaf (overEtaleTopology Y) RingCat.{u}) (F : SheafOfModules.{u} R) :
    (modulePushforwardAlongComposite f R).obj F ≅
      (SheafOfModules.pushforward (restrictedRingIso f R).hom).obj F :=
  (bigToSmallPushforwardIso_modulesNatIso f R).app F

/-- The component of `bigToSmallPushforwardIso_modulesNatIso` at `F` is
`bigToSmallPushforwardIso_modules`. -/
theorem bigToSmallPushforwardIso_modulesNatIso_app {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (R : Sheaf (overEtaleTopology Y) RingCat.{u})
    (F : SheafOfModules.{u} R) :
    (bigToSmallPushforwardIso_modulesNatIso f R).app F =
      bigToSmallPushforwardIso_modules f R F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end
