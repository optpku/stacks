/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Cofiltered.Colimit.SheafPullback
public import ReasLib.CategoryTheory.Sites.ExactMorphismOfSites

/-!
# Pullback sections on cofiltered colimit sites

This file owns the sectionwise filtered-colimit comparison for pulling a
set-valued sheaf from one stage of a cofiltered site diagram to its colimit
site.  The colimit category and its topology are supplied by the lower
`Cofiltered.ColimitTopology` layer.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace CategoryTheory

namespace CofilteredSiteDiagram

namespace ColimitPullback

/-- Pullback of set-valued sheaves along one transition functor of a cofiltered site diagram. -/
noncomputable abbrev stagePullback
    (S : CofilteredSiteDiagram.{u, u, u})
    {i j : S.I} (a : j ⟶ i) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf (S.stageTopology j) (Type u) :=
  (S.stageFunctor a).sheafPullback (Type u) (S.stageTopology i) (S.stageTopology j)

/-- The stage pullback associated to one object of the index over-category. -/
abbrev overPullback
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (A : (Over i)ᵒᵖ) :
    Sheaf (S.stageTopology i) (Type u) ⥤ Sheaf (S.stageTopology A.unop.left) (Type u) :=
  stagePullback S A.unop.hom

/-- The section type obtained by evaluating a stage pullback at the image of an object. -/
abbrev sectionValue
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) : Type u :=
  ((overPullback S A).obj F).obj.obj (op (S.overImage X A))

/-- The adjoint transpose of the canonical pullback-composition comparison. -/
noncomputable def sectionTransition
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (overPullback S A).obj F ⟶
      ((S.stageFunctor f.unop.left).sheafPushforwardContinuous
        (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).obj
        ((overPullback S B).obj F) :=
  let h : f.unop.left ≫ A.unop.hom = B.unop.hom := Over.w f.unop
  let h' :
      (stagePullback S (f.unop.left ≫ A.unop.hom)).obj F =
        (overPullback S B).obj F :=
    congrArg (fun a : B.unop.left ⟶ i => (stagePullback S a).obj F) h
  (((S.stageFunctor f.unop.left).sheafAdjunctionContinuous
    (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv _ _)
    ((S.stageSheafPullbackCompIso (Type u) A.unop.hom f.unop.left).hom.app F ≫
      eqToHom h')

/-- The map on section types induced by an arrow of the opposite over-category. -/
noncomputable def sectionMap
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    sectionValue S F X A ⟶ sectionValue S F X B :=
  let hobj :
      (S.stageFunctor f.unop.left).obj (S.overImage X A) = S.overImage X B :=
    (S.stageFunctor_obj_comp A.unop.hom f.unop.left X).trans
      (congrArg (fun a : B.unop.left ⟶ i => (S.stageFunctor a).obj X) (Over.w f.unop))
  (sectionTransition S F f).hom.app (op (S.overImage X A)) ≫
    eqToHom (congrArg (fun Y => ((overPullback S B).obj F).obj.obj (op Y)) hobj)

/-- The section transition induced by an identity arrow is the identity map. -/
theorem sectionMap_id
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    sectionMap S F X (𝟙 A) = 𝟙 _ := sorry

/-- Section transitions compose along the opposite over-category. -/
theorem sectionMap_comp
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B C : (Over i)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) :
    sectionMap S F X (f ≫ g) = sectionMap S F X f ≫ sectionMap S F X g := sorry

/-- The filtered diagram of sections obtained from pullbacks along the over-category of an index object. -/
noncomputable abbrev sectionDiagram
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := sectionValue S F X A
  map f := sectionMap S F X f
  map_id A := sectionMap_id S F X A
  map_comp f g := sectionMap_comp S F X f g

/-- One canonical leg from the stage-section diagram to the colimit-site pullback section type. -/
noncomputable def comparisonLeg
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    sectionValue S F X A ⟶
      ((((S.stageCoconeFunctor i).sheafPullback
        (Type u) (S.stageTopology i) S.colimitTopology).obj F).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) :=
  let h :
      (S.stageCoconeFunctor A.unop.left).obj (S.overImage X A) =
        (S.stageCoconeFunctor i).obj X :=
    S.ιObj_lower A.unop.hom X
  (((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous
    (Type u) (S.stageTopology A.unop.left) S.colimitTopology).unit.app
    ((overPullback S A).obj F)).hom.app (op (S.overImage X A)) ≫
  (((S.stageCoconeFunctor A.unop.left).sheafPushforwardContinuous
    (Type u) (S.stageTopology A.unop.left) S.colimitTopology).map
    ((compIso (Type u) A.unop.hom).hom.app F)).hom.app
    (op (S.overImage X A)) ≫
  eqToHom (congrArg
    (fun Y => ((((S.stageCoconeFunctor i).sheafPullback
      (Type u) (S.stageTopology i) S.colimitTopology).obj F).obj.obj (op Y))) h)

/-- The canonical comparison legs form a cocone over the stage-section diagram. -/
theorem comparisonLeg_naturality
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i)
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (sectionDiagram S F X).map f ≫ comparisonLeg S F X B =
      comparisonLeg S F X A ≫
        ((Functor.const (Over i)ᵒᵖ).obj
          ((((S.stageCoconeFunctor i).sheafPullback
            (Type u) (S.stageTopology i) S.colimitTopology).obj F).obj.obj
            (op ((S.stageCoconeFunctor i).obj X)))).map f := sorry

/-- The canonical cocone whose colimit map is the pullback-section comparison. -/
noncomputable abbrev comparisonCocone
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Cocone (sectionDiagram S F X) where
  pt :=
    ((((S.stageCoconeFunctor i).sheafPullback
      (Type u) (S.stageTopology i) S.colimitTopology).obj F).obj.obj
      (op ((S.stageCoconeFunctor i).obj X)))
  ι :=
    { app := fun A => comparisonLeg S F X A
      naturality := fun {_ _} f => comparisonLeg_naturality S F X f }

/-- The canonical map from the filtered colimit of stage-pullback sections to the colimit-site
pullback section type. -/
noncomputable def comparison
    (S : CofilteredSiteDiagram.{u, u, u}) {i : S.I}
    (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    colimit (sectionDiagram S F X) ⟶
      ((((S.stageCoconeFunctor i).sheafPullback
        (Type u) (S.stageTopology i) S.colimitTopology).obj F).obj.obj
        (op ((S.stageCoconeFunctor i).obj X))) :=
  colimit.desc _ (comparisonCocone S F X)

/-- Each cocone functor from a stage site to the colimit site is a morphism of sites. -/
@[stacks 0A35 "(1)"]
theorem stageCocone_isMorphismOfSites
    (S : CofilteredSiteDiagram.{u, u, u}) (i : S.I)
    [HasWeakSheafify S.colimitTopology (Type u)]
    [∀ P : (S.stage i)ᵒᵖ ⥤ Type u,
      (S.stageCoconeFunctor i).op.HasLeftKanExtension P] :
    IsExactMorphismOfSites (S.stageTopology i) S.colimitTopology
      (S.stageCoconeFunctor i) := sorry

/-- The canonical filtered-colimit comparison on stage-pullback sections is invertible. -/
@[stacks 0A35 "(2)"]
theorem comparison_isIso
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    IsIso (comparison S F X) := sorry

/-- The source-text bijectivity formulation of the stage-pullback section comparison. -/
theorem comparison_bijective
    (S : CofilteredSiteDiagram.{u, u, u})
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) (X : S.stage i) :
    Function.Bijective (comparison S F X) := sorry

end ColimitPullback

end CofilteredSiteDiagram

end CategoryTheory
