/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.Colimit.SheafPullback
public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily

/-!
# Colimit sheaves of compatible stage families

This layer extends a `CofilteredSiteDiagram.StageFamily` to the explicit
colimit site.  The stage-family data and the colimit-site pullback comparison
are owned by lower layers; this file supplies their reusable assembly and the
set-valued section comparison of Lemma 7.18.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u uI uC vC w

namespace CategoryTheory

namespace CofilteredSiteDiagram

/-- The capabilities needed to pull an `A`-valued compatible stage family to the colimit site:
stage pullbacks for every transition and a left adjoint to every cocone pushforward. -/
class ColimitSheafPullback
    (S : CofilteredSiteDiagram.{uI, uC, vC}) (A : Type w) [Category A] : Prop where
  /-- A sheaf pullback can be formed along each stage transition. -/
  stage {i j : S.I} (a : j ⟶ i) : StageSheafPullback S A a
  /-- The sheaf pushforward along each cocone functor is a right adjoint. -/
  coconeRightAdjoint (i : S.I) :
    ((S.stageCoconeFunctor i).sheafPushforwardContinuous A
      (S.stageTopology i) S.colimitTopology).IsRightAdjoint

attribute [instance] ColimitSheafPullback.stage
attribute [instance] ColimitSheafPullback.coconeRightAdjoint

/-- Existing stagewise sheafification and left-Kan-extension instances provide the colimit
pullback capability. -/
instance ColimitSheafPullback.ofInstances
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [∀ i : S.I, HasWeakSheafify (S.stageTopology i) A]
    [HasWeakSheafify S.colimitTopology A]
    [∀ {i j : S.I} (a : j ⟶ i),
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ i : S.I,
      ∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageCoconeFunctor i).op.HasLeftKanExtension F] :
    ColimitSheafPullback S A where
  stage a := StageSheafPullback.ofInstances a
  coconeRightAdjoint _ := inferInstance

namespace StageFamily

/-- The transition between two stage-family sheaves after pulling them to the colimit site. -/
noncomputable def colimitTransition
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A] (family : StageFamily S A)
    {i j : S.I} (a : j ⟶ i) :
    ((S.stageCoconeFunctor i).sheafPullback A
      (S.stageTopology i) S.colimitTopology).obj (family.obj i) ⟶
      ((S.stageCoconeFunctor j).sheafPullback A
        (S.stageTopology j) S.colimitTopology).obj (family.obj j) :=
  (ColimitPullback.compIso A a).inv.app (family.obj i) ≫
    ((S.stageCoconeFunctor j).sheafPullback A
      (S.stageTopology j) S.colimitTopology).map (family.transition a)

/-- The colimit-site transition at an identity arrow is the identity. -/
theorem colimitTransition_id
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A] (family : StageFamily S A) (i : S.I) :
    colimitTransition family (𝟙 i) =
      𝟙 (((S.stageCoconeFunctor i).sheafPullback A
        (S.stageTopology i) S.colimitTopology).obj (family.obj i)) := sorry

/-- The colimit-site transitions of a compatible family compose along index arrows. -/
theorem colimitTransition_comp
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A] (family : StageFamily S A)
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    colimitTransition family (b ≫ a) =
      colimitTransition family a ≫ colimitTransition family b := sorry

/-- The `S.Iᵒᵖ`-indexed diagram obtained by pulling every member of a compatible stage family
to the colimit site. -/
noncomputable abbrev diagram
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A] (family : StageFamily S A) :
    S.Iᵒᵖ ⥤ Sheaf S.colimitTopology A where
  obj i :=
    ((S.stageCoconeFunctor i.unop).sheafPullback A
      (S.stageTopology i.unop) S.colimitTopology).obj (family.obj i.unop)
  map a := colimitTransition family a.unop
  map_id i := colimitTransition_id family i.unop
  map_comp a b := colimitTransition_comp family a.unop b.unop

/-- Lemma 7.18.4 (09YN): the sheaf on the colimit site assembled from a compatible family of
stage sheaves. -/
@[stacks 09YN]
noncomputable abbrev colimitSheaf
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    [ColimitSheafPullback S A]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology A)]
    (family : StageFamily S A) : Sheaf S.colimitTopology A :=
  colimit (diagram family)

namespace Section

/-- The section type at an over-object for a set-valued compatible stage family. -/
abbrev value
    {S : CofilteredSiteDiagram.{u, u, u}}
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) : Type u :=
  (family.obj A.unop.left).obj.obj (op (S.overImage X A))

/-- The transition map between over-indexed section types. -/
noncomputable def map
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    value family X A ⟶ value family X B :=
  (((S.stageFunctor f.unop.left).sheafAdjunctionContinuous
    (Type u) (S.stageTopology A.unop.left) (S.stageTopology B.unop.left)).homEquiv _ _
    (family.transition f.unop.left)).hom.app (op (S.overImage X A)) ≫
  eqToHom
    (congrArg (fun Y ↦ (family.obj B.unop.left).obj.obj (op Y))
      ((S.stageFunctor_obj_comp A.unop.hom f.unop.left X).trans
        (congrArg (fun a ↦ (S.stageFunctor a).obj X) (Over.w f.unop))))

/-- The over-indexed section transition at an identity arrow is the identity. -/
theorem map_id
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) :
    map family X (𝟙 A) = 𝟙 _ := sorry

/-- The over-indexed section transitions compose. -/
theorem map_comp
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i)
    {A B C : (Over i)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) :
    map family X (f ≫ g) = map family X f ≫ map family X g := sorry

/-- The section diagram indexed by arrows into a fixed stage. -/
noncomputable abbrev diagram
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj A := value family X A
  map f := map family X f
  map_id A := map_id family X A
  map_comp f g := map_comp family X f g

/-- A canonical leg from one stage-family section to the associated section of the colimit
sheaf. -/
noncomputable def comparisonLeg
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) :
    value family X A ⟶
      (family.colimitSheaf).obj.obj (op ((S.stageCoconeFunctor i).obj X)) :=
  (((S.stageCoconeFunctor A.unop.left).sheafAdjunctionContinuous
    (Type u) (S.stageTopology A.unop.left) S.colimitTopology).unit.app
    (family.obj A.unop.left)).hom.app (op (S.overImage X A)) ≫
  eqToHom
    (congrArg
      (fun Y ↦
        (((S.stageCoconeFunctor A.unop.left).sheafPullback
          (Type u) (S.stageTopology A.unop.left) S.colimitTopology).obj
          (family.obj A.unop.left)).obj.obj (op Y))
      (S.ιObj_lower A.unop.hom X)) ≫
  (colimit.ι (family.diagram) (op A.unop.left)).hom.app
    (op ((S.stageCoconeFunctor i).obj X))

/-- The canonical section comparison legs form a cocone. -/
theorem comparisonLeg_naturality
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (diagram family X).map f ≫ comparisonLeg family X B =
      comparisonLeg family X A ≫
        ((Functor.const (Over i)ᵒᵖ).obj
          ((family.colimitSheaf).obj.obj
            (op ((S.stageCoconeFunctor i).obj X)))).map f := sorry

/-- The cocone whose colimit map compares stage-family sections with colimit-sheaf sections. -/
noncomputable abbrev comparisonCocone
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) : Cocone (diagram family X) where
  pt := (family.colimitSheaf).obj.obj (op ((S.stageCoconeFunctor i).obj X))
  ι :=
    { app := fun A ↦ comparisonLeg family X A
      naturality := fun {_ _} f ↦ comparisonLeg_naturality family X f }

/-- The canonical map from the filtered colimit of stage-family sections to the corresponding
section of the colimit sheaf. -/
noncomputable def comparison
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) :
    colimit (diagram family X) ⟶
      (family.colimitSheaf).obj.obj (op ((S.stageCoconeFunctor i).obj X)) :=
  colimit.desc _ (comparisonCocone family X)

/-- The section comparison restricts to its canonical leg on every colimit summand. -/
theorem comparison_ι
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) :
    colimit.ι (diagram family X) A ≫ comparison family X =
      comparisonLeg family X A := sorry

/-- Lemma 7.18.4 (09YN): the filtered-colimit comparison from a compatible set-valued stage
family to its colimit sheaf is an isomorphism on every stage object. -/
@[stacks 09YN]
theorem comparison_isIso
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) :
    IsIso (comparison family X) := sorry

/-- The source-text bijectivity form of the section comparison. -/
theorem comparison_bijective
    {S : CofilteredSiteDiagram.{u, u, u}}
    [ColimitSheafPullback S (Type u)]
    [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology (Type u))]
    (family : StageFamily S (Type u))
    {i : S.I} (X : S.stage i) :
    Function.Bijective (comparison family X) := sorry

end Section

end StageFamily

end CofilteredSiteDiagram

end CategoryTheory
