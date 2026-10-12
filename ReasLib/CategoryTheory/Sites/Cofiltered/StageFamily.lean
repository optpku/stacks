/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.Basic

/-!
# Compatible sheaf families on cofiltered site diagrams

This file owns the stage-level category of compatible sheaf families.  It deliberately
does not use the colimit category or its topology; colimit-site constructions belong to
the chapter-level bridge API built on this module.
-/

@[expose] public section

noncomputable section

open Opposite

universe uI uC vC w

namespace CategoryTheory

namespace CofilteredSiteDiagram

/-- The capability to form the canonical sheaf pullback associated to one transition arrow of a
cofiltered site diagram.  The primitive capability is that the corresponding sheaf pushforward
has a left adjoint; weak sheafification and Kan extensions are sufficient construction data, not
part of the downstream interface. -/
class StageSheafPullback
    (S : CofilteredSiteDiagram.{uI, uC, vC}) (A : Type w) [Category A]
    {i j : S.I} (a : j ⟶ i) : Prop where
  /-- The pushforward along the transition is a right adjoint. -/
  isRightAdjoint :
    ((S.stageFunctor a).sheafPushforwardContinuous A
      (S.stageTopology i) (S.stageTopology j)).IsRightAdjoint

attribute [instance] StageSheafPullback.isRightAdjoint

/-- Existing weak sheafification and left-Kan-extension instances supply the stage-pullback
capability. -/
instance StageSheafPullback.ofInstances
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    {i j : S.I} (a : j ⟶ i)
    [HasWeakSheafify (S.stageTopology j) A]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F] :
    StageSheafPullback S A a where
  isRightAdjoint := inferInstance

namespace StageSheafPullback

/-- The sheaf pullback functor associated to a stage transition. -/
noncomputable abbrev functor
    {S : CofilteredSiteDiagram.{uI, uC, vC}} (A : Type w) [Category A]
    {i j : S.I} (a : j ⟶ i) [StageSheafPullback S A a] :
    Sheaf (S.stageTopology i) A ⥤ Sheaf (S.stageTopology j) A :=
  (S.stageFunctor a).sheafPullback A (S.stageTopology i) (S.stageTopology j)

/-- The pullback along an identity stage transition is canonically the identity functor. -/
noncomputable def idIso
    {S : CofilteredSiteDiagram.{uI, uC, vC}} (A : Type w) [Category A]
    (i : S.I) [StageSheafPullback S A (𝟙 i)] :
    functor A (𝟙 i) ≅ 𝟭 (Sheaf (S.stageTopology i) A) :=
  let e := eqToIso (congrArg Cat.Hom.toFunctor (S.diagram.map_id (op i)))
  Adjunction.leftAdjointIdIso
    ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology i))
    (Functor.sheafPushforwardContinuousId' e A (S.stageTopology i))

/-- Pullback functors along successive stage transitions compose canonically. -/
noncomputable def compIso
    {S : CofilteredSiteDiagram.{uI, uC, vC}} (A : Type w) [Category A]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    [StageSheafPullback S A a]
    [StageSheafPullback S A b]
    [StageSheafPullback S A (b ≫ a)] :
    functor A a ⋙ functor A b ≅ functor A (b ≫ a) :=
  let e := eqToIso (congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op))
  Adjunction.leftAdjointCompIso
    ((S.stageFunctor a).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology j))
    ((S.stageFunctor b).sheafAdjunctionContinuous A
      (S.stageTopology j) (S.stageTopology k))
    ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology k))
    (Functor.sheafPushforwardContinuousComp' e.symm
      A (S.stageTopology i) (S.stageTopology j) (S.stageTopology k))

end StageSheafPullback

/-- Lemma 7.18.4 (09YN): a compatible family of `A`-valued sheaves on the stage sites
of a cofiltered site diagram. -/
@[stacks 09YN]
structure StageFamily
    (S : CofilteredSiteDiagram.{uI, uC, vC}) (A : Type w) [Category A] where
  /-- The sheaf at a stage. -/
  obj (i : S.I) : Sheaf (S.stageTopology i) A
  /-- The transition morphism for an arrow `a : j ⟶ i`. -/
  transition {i j : S.I} (a : j ⟶ i) [StageSheafPullback S A a] :
    (StageSheafPullback.functor A a).obj (obj i) ⟶ obj j
  /-- The transition at an identity arrow is the canonical identity-pullback comparison. -/
  transition_id (i : S.I) [StageSheafPullback S A (𝟙 i)] :
    transition (𝟙 i) = (StageSheafPullback.idIso A i).hom.app (obj i)
  /-- The transition morphisms satisfy the pullback cocycle condition. -/
  transition_comp {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
      [StageSheafPullback S A a]
      [StageSheafPullback S A b]
      [StageSheafPullback S A (b ≫ a)] :
      (StageSheafPullback.compIso A a b).hom.app (obj i) ≫ transition (b ≫ a) =
        (StageSheafPullback.functor A b).map (transition a) ≫ transition b

namespace StageFamily

/-- A morphism of compatible stage families is a componentwise morphism commuting with the
transition maps. -/
@[ext] structure Hom
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F G : StageFamily S A) where
  /-- The component morphism at a stage. -/
  app (i : S.I) : F.obj i ⟶ G.obj i
  /-- The component maps commute with transition morphisms. -/
  comm {i j : S.I} (a : j ⟶ i) [StageSheafPullback S A a] :
    (StageSheafPullback.functor A a).map (app i) ≫ G.transition a =
      F.transition a ≫ app j

/-- Identity component maps commute with the stage-family transitions. -/
theorem Hom.id_comm
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F : StageFamily S A)
    {i j : S.I} (a : j ⟶ i) [StageSheafPullback S A a] :
    (StageSheafPullback.functor A a).map (𝟙 (F.obj i)) ≫ F.transition a =
      F.transition a ≫ 𝟙 (F.obj j) := sorry

/-- The identity morphism of a compatible stage family. -/
def Hom.id
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    (F : StageFamily S A) : Hom F F where
  app _ := 𝟙 _
  comm a := Hom.id_comm F a

/-- Composite component maps commute with the stage-family transitions. -/
theorem Hom.comp_comm
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    {F G H : StageFamily S A} (f : Hom F G) (g : Hom G H)
    {i j : S.I} (a : j ⟶ i) [StageSheafPullback S A a] :
    (StageSheafPullback.functor A a).map (f.app i ≫ g.app i) ≫ H.transition a =
      F.transition a ≫ (f.app j ≫ g.app j) := sorry

/-- Composition of compatible stage-family morphisms. -/
def Hom.comp
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    {F G H : StageFamily S A} (f : Hom F G) (g : Hom G H) : Hom F H where
  app i := f.app i ≫ g.app i
  comm a := Hom.comp_comm f g a

/-- Left identity for compatible stage-family morphisms. -/
theorem Hom.id_comp
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    {F G : StageFamily S A} (f : Hom F G) :
    Hom.comp (Hom.id F) f = f := sorry

/-- Right identity for compatible stage-family morphisms. -/
theorem Hom.comp_id
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    {F G : StageFamily S A} (f : Hom F G) :
    Hom.comp f (Hom.id G) = f := sorry

/-- Associativity for compatible stage-family morphisms. -/
theorem Hom.assoc
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A]
    {F G H I : StageFamily S A} (f : Hom F G) (g : Hom G H) (h : Hom H I) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := sorry

/-- Compatible stage families and their compatible componentwise maps form a category. -/
instance
    {S : CofilteredSiteDiagram.{uI, uC, vC}} {A : Type w} [Category A] :
    Category (StageFamily S A) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp f := Hom.id_comp f
  comp_id f := Hom.comp_id f
  assoc f g h := Hom.assoc f g h

end StageFamily

end CofilteredSiteDiagram

end CategoryTheory
