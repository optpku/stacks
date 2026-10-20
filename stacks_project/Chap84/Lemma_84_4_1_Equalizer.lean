/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.CategoryTheory.Limits.Shapes.Equalizer
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_Proper

/-!
# Small étale unit and fibre-product faces

The adjunction unit of `smallEtaleMorphismOfTopoi f` and the two maps induced by
the projections of `Y ×_X Y` form the parallel pair used by Lemma 84.4.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

/-- The sheaf `f_* f⁻¹ F` on `X_étale`. -/
abbrev smallEtalePushPull (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi f).pushforward.obj
    ((smallEtaleMorphismOfTopoi f).inverseImage.obj F)

/-- `smallEtalePushPull f F` is the pushforward of the inverse image of `F`. -/
theorem smallEtalePushPull_def (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePushPull f F =
      (smallEtaleMorphismOfTopoi f).pushforward.obj
        ((smallEtaleMorphismOfTopoi f).inverseImage.obj F) :=
  rfl

/-- The adjunction unit `F ⟶ f_* f⁻¹ F` of `smallEtaleMorphismOfTopoi f`. -/
def smallEtaleUnit (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    F ⟶ smallEtalePushPull f F :=
  (smallEtaleMorphismOfTopoi f).adjunction.unit.app F

/-- `smallEtaleUnit f F` is the unit of `f_small` at `F`. -/
theorem smallEtaleUnit_eq (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtaleUnit f F = (smallEtaleMorphismOfTopoi f).adjunction.unit.app F :=
  rfl

/-- Direct images of small étale topos morphisms compose by right-adjoint uniqueness
along `smallEtaleMorphismOfTopoiComp`. -/
def smallEtaleComp_pushforward {Z : AlgebraicSpace S} (p : Z ⟶ Y) :
    (smallEtaleMorphismOfTopoi (p ≫ f)).pushforward ≅
      ((smallEtaleMorphismOfTopoi f).comp (smallEtaleMorphismOfTopoi p)).pushforward :=
  ((smallEtaleMorphismOfTopoi (p ≫ f)).adjunction.ofNatIsoLeft
      (smallEtaleMorphismOfTopoiComp p f)).rightAdjointUniq
    ((smallEtaleMorphismOfTopoi f).comp (smallEtaleMorphismOfTopoi p)).adjunction

/-- `smallEtaleComp_pushforward` is the right-adjoint mate of
`smallEtaleMorphismOfTopoiComp`. -/
theorem smallEtaleComp_pushforward_eq {Z : AlgebraicSpace S} (p : Z ⟶ Y) :
    smallEtaleComp_pushforward f p =
      ((smallEtaleMorphismOfTopoi (p ≫ f)).adjunction.ofNatIsoLeft
          (smallEtaleMorphismOfTopoiComp p f)).rightAdjointUniq
        ((smallEtaleMorphismOfTopoi f).comp (smallEtaleMorphismOfTopoi p)).adjunction :=
  rfl

/-- Identification `(p ≫ f)_* (p ≫ f)⁻¹ F ≅ f_* (p_* p⁻¹ f⁻¹ F)`. -/
def smallEtaleCompPushPullIso {Z : AlgebraicSpace S} (p : Z ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePushPull (p ≫ f) F ≅
      (smallEtaleMorphismOfTopoi f).pushforward.obj
        (smallEtalePushPull p ((smallEtaleMorphismOfTopoi f).inverseImage.obj F)) :=
  (smallEtaleComp_pushforward f p).app
      ((smallEtaleMorphismOfTopoi (p ≫ f)).inverseImage.obj F) ≪≫
    ((smallEtaleMorphismOfTopoi f).comp (smallEtaleMorphismOfTopoi p)).pushforward.mapIso
      ((smallEtaleMorphismOfTopoiComp p f).app F)

/-- `smallEtaleCompPushPullIso` is the objectwise composite of
`smallEtaleComp_pushforward` with the inverse-image comparison. -/
theorem smallEtaleCompPushPullIso_eq {Z : AlgebraicSpace S} (p : Z ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtaleCompPushPullIso f p F =
      (smallEtaleComp_pushforward f p).app
          ((smallEtaleMorphismOfTopoi (p ≫ f)).inverseImage.obj F) ≪≫
        ((smallEtaleMorphismOfTopoi f).comp
            (smallEtaleMorphismOfTopoi p)).pushforward.mapIso
          ((smallEtaleMorphismOfTopoiComp p f).app F) :=
  rfl

/-- Transport of `g_* g⁻¹ F` along an equality of morphisms to `X`. -/
def smallEtalePushPullCongr {Z : AlgebraicSpace S} {g g' : Z ⟶ X} (h : g = g')
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePushPull g F ≅ smallEtalePushPull g' F :=
  eqToIso (congrArg (fun q ↦ smallEtalePushPull q F) h)

/-- `smallEtalePushPullCongr` is `eqToIso` of `smallEtalePushPull` along the given
equality. -/
theorem smallEtalePushPullCongr_eq {Z : AlgebraicSpace S} {g g' : Z ⟶ X} (h : g = g')
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePushPullCongr h F =
      eqToIso (congrArg (fun q ↦ smallEtalePushPull q F) h) :=
  rfl

/-- The comparison `f_* f⁻¹ F ⟶ g_* g⁻¹ F` induced by a map `p : Y ×_X Y ⟶ Y` over
`X`, where `g` is the structure morphism `Y ×_X Y ⟶ X`. -/
def smallEtaleFace (p : pullback f f ⟶ Y) (hp : p ≫ f = pullback.fst f f ≫ f)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePushPull f F ⟶ smallEtalePushPull (pullback.fst f f ≫ f) F :=
  (smallEtaleMorphismOfTopoi f).pushforward.map
      ((smallEtaleMorphismOfTopoi p).adjunction.unit.app
        ((smallEtaleMorphismOfTopoi f).inverseImage.obj F)) ≫
    (smallEtaleCompPushPullIso f p F).inv ≫ (smallEtalePushPullCongr hp F).hom

/-- `smallEtaleFace` is `f_*` of the unit of `p_small`, conjugated by the composition
iso and the structure-morphism comparison. -/
theorem smallEtaleFace_eq (p : pullback f f ⟶ Y)
    (hp : p ≫ f = pullback.fst f f ≫ f)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtaleFace f p hp F =
      (smallEtaleMorphismOfTopoi f).pushforward.map
          ((smallEtaleMorphismOfTopoi p).adjunction.unit.app
            ((smallEtaleMorphismOfTopoi f).inverseImage.obj F)) ≫
        (smallEtaleCompPushPullIso f p F).inv ≫
          (smallEtalePushPullCongr hp F).hom :=
  rfl

/-- The first projection map `f_* f⁻¹ F ⟶ g_* g⁻¹ F` induced by
`pullback.fst f f : Y ×_X Y ⟶ Y`. -/
def smallEtaleFstMap (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePushPull f F ⟶ smallEtalePushPull (pullback.fst f f ≫ f) F :=
  smallEtaleFace f (pullback.fst f f) rfl F

/-- `smallEtaleFstMap` is the face of the first projection. -/
theorem smallEtaleFstMap_eq (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtaleFstMap f F = smallEtaleFace f (pullback.fst f f) rfl F :=
  rfl

/-- The second projection map `f_* f⁻¹ F ⟶ g_* g⁻¹ F` induced by
`pullback.snd f f : Y ×_X Y ⟶ Y`. -/
def smallEtaleSndMap (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePushPull f F ⟶ smallEtalePushPull (pullback.fst f f ≫ f) F :=
  smallEtaleFace f (pullback.snd f f) pullback.condition.symm F

/-- `smallEtaleSndMap` is the face of the second projection, transported along
`pullback.condition`. -/
theorem smallEtaleSndMap_eq (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtaleSndMap f F =
      smallEtaleFace f (pullback.snd f f) pullback.condition.symm F :=
  rfl

/-- The unit `F ⟶ f_* f⁻¹ F` equalizes the two projection maps
`f_* f⁻¹ F ⇉ g_* g⁻¹ F`. -/
theorem smallEtaleUnit_equalizes (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtaleUnit f F ≫ smallEtaleFstMap f F =
      smallEtaleUnit f F ≫ smallEtaleSndMap f F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
