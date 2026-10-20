/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Big
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small étale morphism relations

This leaf owns the cross-layer composition API for the small and big étale
topoi.  Its API lives directly below `Etale.SmallToBig`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

variable {S T : Scheme.{u}}

/-- The morphism of topoi induced by small étale base change along `f`. -/
noncomputable def smallMorphism (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    MorphismOfTopoiIn S.smallEtaleTopology T.smallEtaleTopology :=
  CategoryTheory.IsMorphismOfSites.toMorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
    (smallEtalePullback f)

/-- Restriction to small étale objects commutes with base change on the big étale slices. -/
private noncomputable def pullbackRelocalizationIso (f : T ⟶ S) :
    relocalizationFunctor (𝟙 S) ⋙ Big.pullback f ≅
      smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T) :=
  Functor.associator (MorphismProperty.Over.forget @Etale ⊤ S)
      (Over.map (𝟙 S)) (Big.pullback f) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget @Etale ⊤ S)
      (Functor.isoWhiskerRight (Over.mapId S) (Big.pullback f) ≪≫
        Functor.leftUnitor (Big.pullback f)) ≪≫
    (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f).symm ≪≫
    Functor.isoWhiskerLeft (smallEtalePullback f)
      ((Functor.rightUnitor (MorphismProperty.Over.forget @Etale ⊤ T)).symm ≪≫
        Functor.isoWhiskerLeft (MorphismProperty.Over.forget @Etale ⊤ T) (Over.mapId T).symm)

/-- Restriction from big to small étale sheaves commutes naturally with direct image. -/
@[no_expose]
noncomputable def pushforwardRestrictIso (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    (Big.morphismOfTopoi f).pushforward ⋙ (siteMorphismOfTopoi S).pushforward ≅
      (siteMorphismOfTopoi T).pushforward ⋙ (smallMorphism f).pushforward :=
  Functor.isoWhiskerRight (Big.directImageIsoPullbackPresentation f)
      (siteMorphismOfTopoi S).pushforward ≪≫
    Functor.sheafPushforwardContinuousComp (relocalizationFunctor (𝟙 S))
      (Big.pullback f) (Type (u + 1)) S.smallEtaleTopology
      (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale) ≪≫
    @Functor.sheafPushforwardContinuousIso _ _ _ _ _ _ (pullbackRelocalizationIso f)
      (Type (u + 1)) _ S.smallEtaleTopology (T.overGrothendieckTopology @Etale)
      (Functor.isContinuous_comp (relocalizationFunctor (𝟙 S))
        (Big.pullback f) S.smallEtaleTopology
        (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale))
      (Functor.isContinuous_comp (smallEtalePullback f)
        (relocalizationFunctor (𝟙 T)) S.smallEtaleTopology T.smallEtaleTopology
        (T.overGrothendieckTopology @Etale)) ≪≫
    (Functor.sheafPushforwardContinuousComp (smallEtalePullback f)
      (relocalizationFunctor (𝟙 T)) (Type (u + 1))
      S.smallEtaleTopology T.smallEtaleTopology (T.overGrothendieckTopology @Etale)).symm

/-- The restriction of a big étale direct image is canonically isomorphic to the small
étale direct image of the restricted sheaf. -/
noncomputable def bigToSmallPushforwardIso (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1))) :
    (siteMorphismOfTopoi S).pushforward.obj
        ((Big.morphismOfTopoi f).pushforward.obj F) ≅
      (smallMorphism f).pushforward.obj
        ((siteMorphismOfTopoi T).pushforward.obj F) :=
  (pushforwardRestrictIso f).app F

/-- The direct image for the small etale morphism is computed by evaluating on
the base-changed small etale object. -/
@[stacks 021I]
theorem smallMorphism_pushforward_obj_obj
    (f : T ⟶ S) [HasSheafify T.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) (U : S.Etale) :
    (((smallMorphism f) _*).obj F).1.obj (op U) =
      F.1.obj (op ((smallEtalePullback f).obj U)) := sorry

/-- The small-to-big étale morphism factors through the big étale morphism. -/
theorem morphism_eq_comp_big (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    morphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (Etale.Big.morphismOfTopoi f)
        (morphismOfTopoi (𝟙 T)) := sorry

/-- The square comparing small and big étale morphisms commutes. -/
theorem smallMorphism_comp_site (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    MorphismOfTopoiIn.comp
        (smallMorphism f)
        (siteMorphismOfTopoi T) =
      MorphismOfTopoiIn.comp
        (siteMorphismOfTopoi S)
        (Etale.Big.morphismOfTopoi f) := sorry

/-- The small étale morphism has the expanded big-site factorization. -/
theorem smallMorphism_eq_comp_big (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    smallMorphism f =
      MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (siteMorphismOfTopoi S)
          (Etale.Big.morphismOfTopoi f))
        (morphismOfTopoi (𝟙 T)) := sorry

/-- The small étale morphism is the direct composite of the site morphism
with small-to-big relocalization. -/
theorem smallMorphism_eq_comp (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))] :
    smallMorphism f =
      MorphismOfTopoiIn.comp
        (siteMorphismOfTopoi S)
        (morphismOfTopoi f) := sorry

/-- Small étale morphisms of topoi compose along composition of scheme morphisms. -/
theorem smallMorphism_comp
    {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (smallMorphism g) (smallMorphism f) =
      smallMorphism (f ≫ g) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig
