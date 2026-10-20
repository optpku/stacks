module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Big
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.CategoryTheory.Sites.Over.Adjunction

/-!
# Big versus small étale direct images of algebraic spaces

Restriction from the big étale slice site to the small étale site commutes with
direct image. The comparison is induced by the natural isomorphism between
`smallEtaleToBig X ⋙ Over.pullback f` and `etaleBaseChange f ⋙ spacesEtaleToBig Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

/-- The inclusion of the small étale site of `X` into the big étale slice
`(Spaces/X)_étale`. -/
abbrev smallEtaleToBig {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite X ⥤ Over X :=
  smallEtaleToSpaces X ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ X

/-- `smallEtaleToBig X` is the composite of `smallEtaleToSpaces` with the forgetful
functor from étale objects over `X` to `Over X`. -/
theorem smallEtaleToBig_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleToBig X =
      smallEtaleToSpaces X ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ X :=
  rfl

/-- On objects, `smallEtaleToBig X` sends a scheme étale over `X` to the same
morphism viewed in `Over X`. -/
theorem smallEtaleToBig_obj_hom {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    ((smallEtaleToBig X).obj U).hom = U.hom :=
  rfl

/-- The forgetful functor from the étale slice `X_spaces,étale` to `(Spaces/X)_étale`. -/
abbrev spacesEtaleToBig {S : Scheme.{u}} (X : AlgebraicSpace S) :
    spacesEtaleSite X ⥤ Over X :=
  MorphismProperty.Over.forget (@Etale S) ⊤ X

/-- `smallEtaleToBig X` factors through the spaces-étale site of `X`. -/
theorem smallEtaleToBig_eq_comp {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleToBig X = smallEtaleToSpaces X ⋙ spacesEtaleToBig X :=
  rfl

/-- The forgetful functor `X_spaces,étale ⥤ (Spaces/X)_étale` is continuous. -/
instance spacesEtaleToBig_isContinuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (spacesEtaleToBig X).IsContinuous (spacesEtaleTopology X) (overEtaleTopology X) :=
  sorry

/-- The inclusion `X_étale ⥤ (Spaces/X)_étale` is continuous. -/
instance smallEtaleToBig_isContinuous {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleToBig X).IsContinuous (smallEtaleTopology X) (overEtaleTopology X) :=
  Functor.isContinuous_comp (smallEtaleToSpaces X) (spacesEtaleToBig X)
    (smallEtaleTopology X) (spacesEtaleTopology X) (overEtaleTopology X)

/-- Restriction of type-valued sheaves from `(Spaces/X)_étale` to `X_étale`. -/
abbrev restrictToSmallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleToBig X).sheafPushforwardContinuous (Type (u + 1))
    (smallEtaleTopology X) (overEtaleTopology X)

/-- `restrictToSmallEtale X` is continuous sheaf pushforward along `smallEtaleToBig X`. -/
theorem restrictToSmallEtale_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    restrictToSmallEtale X =
      (smallEtaleToBig X).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (overEtaleTopology X) :=
  rfl

/-- Sections of a restricted sheaf on `X_étale` are the original sections on the
image object in `(Spaces/X)_étale`. -/
theorem restrictToSmallEtale_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : smallEtaleSite X) :
    ((restrictToSmallEtale X).obj F).obj.obj (op U) =
      F.obj.obj (op ((smallEtaleToBig X).obj U)) :=
  rfl

/-- Restriction of abelian sheaves from `(Spaces/X)_étale` to `X_étale`. -/
abbrev restrictToSmallEtaleAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (smallEtaleToBig X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (overEtaleTopology X)

/-- `restrictToSmallEtaleAbelian X` is continuous sheaf pushforward along
`smallEtaleToBig X`. -/
theorem restrictToSmallEtaleAbelian_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    restrictToSmallEtaleAbelian X =
      (smallEtaleToBig X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (overEtaleTopology X) :=
  rfl

variable {S : Scheme.{u}}

/-- Direct image of type-valued sheaves on big étale slice sites along `f : Y ⟶ X`. -/
abbrev bigPushforward {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  etaleTopology.overMapPushforward (Type (u + 1)) f

/-- `bigPushforward f` is slice-site direct image along `Over.pullback f`. -/
theorem bigPushforward_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    bigPushforward f = etaleTopology.overMapPushforward (Type (u + 1)) f :=
  rfl

/-- Direct image of abelian sheaves on big étale slice sites along `f : Y ⟶ X`. -/
abbrev bigPushforwardAbelian {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  etaleTopology.overMapPushforward AddCommGrpCat.{u + 1} f

/-- `bigPushforwardAbelian f` is slice-site direct image of abelian sheaves. -/
theorem bigPushforwardAbelian_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    bigPushforwardAbelian f =
      etaleTopology.overMapPushforward AddCommGrpCat.{u + 1} f :=
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
  Functor.associator (smallEtaleToSpaces X) (spacesEtaleToBig X) (Over.pullback f) ≪≫
    Functor.isoWhiskerLeft (smallEtaleToSpaces X)
      (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale S) (Q := ⊤) f).symm ≪≫
    (Functor.associator (smallEtaleToSpaces X) (spacesEtalePullback f)
        (spacesEtaleToBig Y)).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback f)
      (spacesEtaleToBig Y)

/-- Small étale pushforward of a restricted sheaf is continuous pushforward along
`etaleBaseChange f ⋙ spacesEtaleToBig Y`. -/
def restrictThenSmallPushforwardIso {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    restrictToSmallEtale Y ⋙ sheafPushforwardType f ≅
      (etaleBaseChange f ⋙ spacesEtaleToBig Y).sheafPushforwardContinuous
        (Type (u + 1)) (smallEtaleTopology X) (overEtaleTopology Y) :=
  Functor.isoWhiskerLeft ((spacesEtaleToBig Y).sheafPushforwardContinuous (Type (u + 1))
      (spacesEtaleTopology Y) (overEtaleTopology Y))
    (Functor.isoWhiskerRight (smallEtalePresentationUnitIso Y).symm
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

/-- The two presentations of the étale site square induce naturally isomorphic
pushforwards of `R`-modules over the ring sheaf obtained by restricting `R` along
`smallEtaleToBig X ⋙ Over.pullback f`, using `restrictedRingIso` to compare scalars. -/
def bigToSmallPushforwardIso_modulesNatIso {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (R : Sheaf (overEtaleTopology Y) RingCat.{u}) :
    modulePushforwardAlongComposite f R ≅
      SheafOfModules.pushforward (restrictedRingIso f R).hom :=
  SheafOfModules.pushforwardNatIso (𝟙 _) (pullbackRelocalizationIso f).symm

/-- The pushforwards of an `R`-module along the two presentations of the étale
site square are canonically isomorphic over the restriction of `R` along
`smallEtaleToBig X ⋙ Over.pullback f`, with scalars compared by `restrictedRingIso`. -/
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
