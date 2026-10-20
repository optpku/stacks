/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian.ActionEquivalence
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.DescentData

/-!
# Descent for cartesian groupoid schemes

This module constructs the equivalence between groupoid schemes cartesian over a Čech
groupoid and descent data for the corresponding morphism of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.CartesianOver

open Scheme.DescentData
open GroupoidScheme.Action.System

/-! This section identifies actions of the Čech groupoid with chosen descent data. -/

/-- The source and target maps of the Čech groupoid form the pullback of `f` with itself. -/
theorem cechPair_isPullback {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    IsPullback
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).t.left
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).s.left f.left f.left := sorry

/-- The chosen pairwise overlap carried by the Čech groupoid. -/
noncomputable def cechPair {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Limits.ChosenPullback f.left f.left where
  pullback := (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).R.left
  p₁ := (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).t.left
  p₂ := (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).s.left
  condition := (cechPair_isPullback f).w
  isLimit := (cechPair_isPullback f).isLimit

/-- The canonical pullback used for the middle two legs of the triple Čech overlap. -/
noncomputable def cechTripleMiddle {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) :
    Limits.ChosenPullback (cechPair f).p₂ (cechPair f).p₁ where
  pullback := Limits.pullback (cechPair f).p₂ (cechPair f).p₁
  p₁ := Limits.pullback.fst (cechPair f).p₂ (cechPair f).p₁
  p₂ := Limits.pullback.snd (cechPair f).p₂ (cechPair f).p₁
  condition := Limits.pullback.condition
  isLimit := Limits.PullbackCone.mkSelfIsLimit (Limits.pullback.isLimit _ _)

/-- The first projection from the chosen triple Čech overlap. -/
noncomputable def cechTripleFirst {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) : (cechTripleMiddle f).pullback ⟶ X.left :=
  (cechTripleMiddle f).p₁ ≫ (cechPair f).p₁

/-- The third projection from the chosen triple Čech overlap. -/
noncomputable def cechTripleThird {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) : (cechTripleMiddle f).pullback ⟶ X.left :=
  (cechTripleMiddle f).p₂ ≫ (cechPair f).p₂

/-- The first and third triple-overlap projections have the same image in `Y`. -/
theorem cechTripleLift_condition {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) :
    cechTripleFirst f ≫ f.left = cechTripleThird f ≫ f.left := sorry

/-- The map from the chosen triple overlap to the first-third pairwise overlap. -/
noncomputable def cechTripleLift {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) : (cechTripleMiddle f).pullback ⟶ (cechPair f).pullback :=
  (cechPair f).isPullback.lift (cechTripleFirst f) (cechTripleThird f)
    (cechTripleLift_condition f)

/-- The triple-to-pair map has the prescribed first projection. -/
theorem cechTripleLift_p₁ {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) : cechTripleLift f ≫ (cechPair f).p₁ = cechTripleFirst f := sorry

/-- The triple-to-pair map has the prescribed second projection. -/
theorem cechTripleLift_p₂ {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) : cechTripleLift f ≫ (cechPair f).p₂ = cechTripleThird f := sorry

/-- The triple-to-pair map is compatible with the common map to `Y`. -/
theorem cechTripleLift_p {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) :
    cechTripleLift f ≫ (cechPair f).p = cechTripleFirst f ≫ f.left := sorry

/-- The first displayed projection of the triple overlap is the chosen one. -/
theorem cechTriple_hp₁ {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) :
    (cechTripleMiddle f).p₁ ≫ (cechPair f).p₁ = cechTripleFirst f := sorry

/-- The third displayed projection of the triple overlap is the chosen one. -/
theorem cechTriple_hp₃ {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) :
    (cechTripleMiddle f).p₂ ≫ (cechPair f).p₂ = cechTripleThird f := sorry

/-- The chosen triple overlap for the Čech groupoid. -/
noncomputable def cechTriple {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Limits.ChosenPullback₃ (cechPair f) (cechPair f) (cechPair f) where
  chosenPullback := cechTripleMiddle f
  p := cechTripleFirst f ≫ f.left
  p₁ := cechTripleFirst f
  p₃ := cechTripleThird f
  l :=
    { f := cechTripleLift f
      f_p₁ := cechTripleLift_p₁ f
      f_p₂ := cechTripleLift_p₂ f
      f_p := cechTripleLift_p f }
  hp₁ := cechTriple_hp₁ f
  hp₃ := cechTriple_hp₃ f

/-- Forgetting the ambient base from a nested pullback square leaves a pullback square of
schemes. -/
theorem iteratedPullback_isPullback {S : Scheme.{u}} {B E : Over S}
    (p : E ⟶ B) (V : Over B) :
    IsPullback
      (Limits.pullback.fst V.hom p).left (Limits.pullback.snd V.hom p).left
      V.hom.left p.left := sorry

/-- Pullback in `Over S`, followed by forgetting the ambient base, agrees with pullback of
schemes. -/
noncomputable def iteratedPullbackIso {S : Scheme.{u}} {B E : Over S}
    (p : E ⟶ B) (V : Over B) :
    E.iteratedSliceForward.obj ((Over.pullback p).obj V) ≅
      (Over.pullback p.left).obj (B.iteratedSliceForward.obj V) :=
  Over.isoMk (iteratedPullback_isPullback p V).isoPullback
    (iteratedPullback_isPullback p V).isoPullback_hom_snd

/-- The nested-pullback comparison expressed in the scheme pseudofunctor presentation. -/
noncomputable def descentPullbackIso {S : Scheme.{u}} {B E : Over S}
    (p : E ⟶ B) (V : Over B) :
    E.iteratedSliceForward.obj ((Over.pullback p).obj V) ≅
      (Scheme.overPseudofunctor.map (Quiver.Hom.toLoc p.left.op)).toFunctor.obj
        (B.iteratedSliceForward.obj V) :=
  iteratedPullbackIso p V ≪≫
    (eqToIso (congrArg (fun F ↦ F.obj (B.iteratedSliceForward.obj V))
      (Scheme.overPseudofunctor_map p.left))).symm

/-- A Čech-groupoid action isomorphism as a chosen pairwise descent isomorphism. -/
noncomputable def actionDescentIso {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    (Scheme.overPseudofunctor.map (cechPair f).p₁.op.toLoc).toFunctor.obj
          ((GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U.iteratedSliceForward.obj
            (GroupoidScheme.Action.obj A)) ≅
      (Scheme.overPseudofunctor.map (cechPair f).p₂.op.toLoc).toFunctor.obj
          ((GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U.iteratedSliceForward.obj
            (GroupoidScheme.Action.obj A)) :=
  (descentPullbackIso
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).t
      (GroupoidScheme.Action.obj A)).symm ≪≫
    (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).R.iteratedSliceForward.mapIso
      (GroupoidScheme.Action.iso A) ≪≫
    descentPullbackIso
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).s
      (GroupoidScheme.Action.obj A)

/-- The component family underlying the chosen descent datum of a Čech-groupoid action. -/
noncomputable def actionDescentObjects {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f))
    (_ : PUnit.{1}) : Over X.left :=
  (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U.iteratedSliceForward.obj
    (GroupoidScheme.Action.obj A)

/-- The pairwise comparison family underlying the chosen descent datum of an action. -/
noncomputable def actionDescentHoms {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    ∀ i j : PUnit.{1},
      (Scheme.overPseudofunctor.map (cechPair f).p₁.op.toLoc).toFunctor.obj
          (actionDescentObjects f A i) ⟶
        (Scheme.overPseudofunctor.map (cechPair f).p₂.op.toLoc).toFunctor.obj
          (actionDescentObjects f A j) :=
  fun _ _ ↦ (actionDescentIso f A).hom

/-- The pairwise comparison obtained from an action satisfies the chosen triple-overlap
cocycle. -/
theorem actionDescentIso_cocycle {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    let pull := @Pseudofunctor.DescentData'.pullHom'
      Scheme _ Scheme.overPseudofunctor PUnit.{1} Y.left
      (fun _ ↦ X.left) (fun _ ↦ f.left) (fun _ _ ↦ cechPair f)
      (actionDescentObjects f A) (actionDescentObjects f A) (actionDescentHoms f A)
    @pull _ (cechTriple f).p PUnit.unit PUnit.unit
          (cechTriple f).p₁ (cechTriple f).p₂
          (cechTriple f).w₁ (cechTriple f).w₂ ≫
        @pull _ (cechTriple f).p PUnit.unit PUnit.unit
          (cechTriple f).p₂ (cechTriple f).p₃
          (cechTriple f).w₂ (cechTriple f).w₃ =
      @pull _ (cechTriple f).p PUnit.unit PUnit.unit
        (cechTriple f).p₁ (cechTriple f).p₃
        (cechTriple f).w₁ (cechTriple f).w₃ := sorry

/-- A Čech-groupoid action gives chosen scheme descent data. -/
noncomputable def actionToChosenObj {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f) :=
  Chosen.ofIso
    (fun _ : PUnit.{1} ↦ X.left) (fun _ : PUnit.{1} ↦ f.left)
    (fun _ _ ↦ cechPair f) (fun _ _ _ ↦ cechTriple f)
    (actionDescentObjects f A) (fun _ _ ↦ actionDescentIso f A)
    (fun _ _ _ ↦ actionDescentIso_cocycle f A)

/-- An action morphism commutes with the chosen descent comparisons. -/
theorem actionToChosenMap_comm {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    {A B : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)} (a : A ⟶ B) :
    ∀ i j : PUnit.{1},
      (Scheme.overPseudofunctor.map (cechPair f).p₁.op.toLoc).toFunctor.map
          ((GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U.iteratedSliceForward.map
            (GroupoidScheme.Action.hom a)) ≫
        (actionToChosenObj f B).hom i j =
      (actionToChosenObj f A).hom i j ≫
        (Scheme.overPseudofunctor.map (cechPair f).p₂.op.toLoc).toFunctor.map
          ((GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U.iteratedSliceForward.map
            (GroupoidScheme.Action.hom a)) := sorry

/-- A morphism of Čech-groupoid actions gives a morphism of chosen descent data. -/
noncomputable def actionToChosenMap {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    {A B : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)} (a : A ⟶ B) :
    actionToChosenObj f A ⟶ actionToChosenObj f B where
  hom := fun _ ↦
    (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U.iteratedSliceForward.map
      (GroupoidScheme.Action.hom a)
  comm := actionToChosenMap_comm f a

/-- The action-to-chosen-descent construction preserves identities. -/
theorem actionToChosenMap_id {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    actionToChosenMap f (𝟙 A) = 𝟙 (actionToChosenObj f A) := sorry

/-- The action-to-chosen-descent construction preserves composition. -/
theorem actionToChosenMap_comp {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {A B C : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)}
    (a : A ⟶ B) (b : B ⟶ C) :
    actionToChosenMap f (a ≫ b) = actionToChosenMap f a ≫ actionToChosenMap f b := sorry

/-- The concrete functor from Čech-groupoid actions to chosen descent data. -/
noncomputable def actionToChosen {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    GroupoidScheme.Action (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f) ⥤
      Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
        (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
        (fun _ _ _ ↦ cechTriple f) where
  obj := actionToChosenObj f
  map := actionToChosenMap f
  map_id := actionToChosenMap_id f
  map_comp := actionToChosenMap_comp f

/-- The nested slice object underlying the action recovered from chosen descent data. -/
noncomputable def chosenActionUnderlying {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    Over (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U :=
  (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).U.iteratedSliceBackward.obj
    (D.obj PUnit.unit)

/-- The action isomorphism recovered from a chosen Čech descent datum. -/
noncomputable def chosenActionIso {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    let G := GroupoidScheme.pullback (GroupoidScheme.discrete Y) f
    (Over.pullback G.t).obj
          (chosenActionUnderlying f D) ≅
      (Over.pullback G.s).obj
          (chosenActionUnderlying f D) :=
  let G := GroupoidScheme.pullback (GroupoidScheme.discrete Y) f
  let eR := G.R.iteratedSliceEquiv
  let eU := G.U.iteratedSliceEquiv
  let rBackward := G.R.iteratedSliceBackward
  let tLeft := G.t.left
  let sLeft := G.s.left
  eR.unitIso.app
        ((Over.pullback G.t).obj (chosenActionUnderlying f D)) ≪≫
    rBackward.mapIso
        (descentPullbackIso G.t (chosenActionUnderlying f D) ≪≫
          (Scheme.overPseudofunctor.map
            tLeft.op.toLoc).toFunctor.mapIso
            (eU.counitIso.app (D.obj PUnit.unit)) ≪≫
          Chosen.iso
            (fun _ : PUnit.{1} ↦ X.left) (fun _ : PUnit.{1} ↦ f.left)
            (fun _ _ ↦ cechPair f) (fun _ _ _ ↦ cechTriple f) D PUnit.unit PUnit.unit ≪≫
          ((Scheme.overPseudofunctor.map
            sLeft.op.toLoc).toFunctor.mapIso
            (eU.counitIso.app (D.obj PUnit.unit))).symm ≪≫
          (descentPullbackIso G.s (chosenActionUnderlying f D)).symm) ≪≫
    (eR.unitIso.app
      ((Over.pullback G.s).obj (chosenActionUnderlying f D))).symm

/-- The recovered action isomorphism satisfies the unit law. -/
theorem chosenActionIso_unit {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    GroupoidScheme.Action.IsUnital
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)
      (chosenActionUnderlying f D) (chosenActionIso f D) := sorry

/-- The recovered action isomorphism satisfies the cocycle law. -/
theorem chosenActionIso_cocycle {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    GroupoidScheme.Action.IsCocycle
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)
      (chosenActionUnderlying f D) (chosenActionIso f D) := sorry

/-- A chosen Čech descent datum gives a groupoid action. -/
noncomputable def chosenToActionObj {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    GroupoidScheme.Action (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f) :=
  GroupoidScheme.Action.ofIso (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)
    (chosenActionUnderlying f D) (chosenActionIso f D)
    (chosenActionIso_unit f D) (chosenActionIso_cocycle f D)

/-- A chosen descent morphism respects the recovered action isomorphisms. -/
theorem chosenToActionMap_compatibility {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    {D E : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)} (a : D ⟶ E) :
    (Over.pullback (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).t).map
          ((GroupoidScheme.pullback
            (GroupoidScheme.discrete Y) f).U.iteratedSliceBackward.map (a.hom PUnit.unit)) ≫
        (chosenActionIso f E).hom =
      (chosenActionIso f D).hom ≫
        (Over.pullback (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).s).map
          ((GroupoidScheme.pullback
            (GroupoidScheme.discrete Y) f).U.iteratedSliceBackward.map
              (a.hom PUnit.unit)) := sorry

/-- A chosen descent morphism gives a morphism of the recovered actions. -/
noncomputable def chosenToActionMap {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    {D E : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)} (a : D ⟶ E) :
    chosenToActionObj f D ⟶ chosenToActionObj f E :=
  Hom.ofMap
    ((GroupoidScheme.pullback
      (GroupoidScheme.discrete Y) f).U.iteratedSliceBackward.map (a.hom PUnit.unit))
    ⟨(chosenToActionMap_compatibility f a).symm⟩

/-- The chosen-descent-to-action construction preserves identities. -/
theorem chosenToActionMap_id {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    chosenToActionMap f (𝟙 D) = 𝟙 (chosenToActionObj f D) := sorry

/-- The chosen-descent-to-action construction preserves composition. -/
theorem chosenToActionMap_comp {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {D E Q : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)} (a : D ⟶ E) (b : E ⟶ Q) :
    chosenToActionMap f (a ≫ b) = chosenToActionMap f a ≫ chosenToActionMap f b := sorry

/-- The concrete functor from chosen Čech descent data to groupoid actions. -/
noncomputable def chosenToAction {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
        (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
        (fun _ _ _ ↦ cechTriple f) ⥤
      GroupoidScheme.Action (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f) where
  obj := chosenToActionObj f
  map := chosenToActionMap f
  map_id := chosenToActionMap_id f
  map_comp := chosenToActionMap_comp f

/-- The underlying component of the action-to-descent-to-action unit. -/
noncomputable def actionChosenUnitUnderlyingIso {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    GroupoidScheme.Action.obj A ≅
      GroupoidScheme.Action.obj (chosenToActionObj f (actionToChosenObj f A)) :=
  let G := GroupoidScheme.pullback (GroupoidScheme.discrete Y) f
  let eU := G.U.iteratedSliceEquiv
  eU.unitIso.app (GroupoidScheme.Action.obj A)

/-- The forward unit component respects the action isomorphisms. -/
theorem actionChosenUnitHom_compatibility {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    (Over.pullback (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).t).map
          (actionChosenUnitUnderlyingIso f A).hom ≫
        (GroupoidScheme.Action.iso
          (chosenToActionObj f (actionToChosenObj f A))).hom =
      (GroupoidScheme.Action.iso A).hom ≫
        (Over.pullback (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).s).map
          (actionChosenUnitUnderlyingIso f A).hom := sorry

/-- The inverse unit component respects the action isomorphisms. -/
theorem actionChosenUnitInv_compatibility {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    (Over.pullback (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).t).map
          (actionChosenUnitUnderlyingIso f A).inv ≫
        (GroupoidScheme.Action.iso A).hom =
      (GroupoidScheme.Action.iso
          (chosenToActionObj f (actionToChosenObj f A))).hom ≫
        (Over.pullback (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f).s).map
          (actionChosenUnitUnderlyingIso f A).inv := sorry

/-- The forward morphism of the action-to-descent-to-action unit. -/
noncomputable def actionChosenUnitHom {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    A ⟶ chosenToActionObj f (actionToChosenObj f A) :=
  Hom.ofMap (actionChosenUnitUnderlyingIso f A).hom
    ⟨(actionChosenUnitHom_compatibility f A).symm⟩

/-- The inverse morphism of the action-to-descent-to-action unit. -/
noncomputable def actionChosenUnitInv {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    chosenToActionObj f (actionToChosenObj f A) ⟶ A :=
  Hom.ofMap (actionChosenUnitUnderlyingIso f A).inv
    ⟨(actionChosenUnitInv_compatibility f A).symm⟩

/-- The unit components compose to the identity on the original action. -/
theorem actionChosenUnit_hom_inv_id {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    actionChosenUnitHom f A ≫ actionChosenUnitInv f A = 𝟙 A := sorry

/-- The unit components compose to the identity on the reconstructed action. -/
theorem actionChosenUnit_inv_hom_id {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    actionChosenUnitInv f A ≫ actionChosenUnitHom f A =
      𝟙 (chosenToActionObj f (actionToChosenObj f A)) := sorry

/-- The action-to-descent-to-action unit component. -/
noncomputable def actionChosenUnitComponentIso {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y)
    (A : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) :
    A ≅ chosenToActionObj f (actionToChosenObj f A) where
  hom := actionChosenUnitHom f A
  inv := actionChosenUnitInv f A
  hom_inv_id := actionChosenUnit_hom_inv_id f A
  inv_hom_id := actionChosenUnit_inv_hom_id f A

/-- The action unit components are natural. -/
theorem actionChosenUnit_naturality {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    {A B : GroupoidScheme.Action
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)} (a : A ⟶ B) :
    a ≫ (actionChosenUnitComponentIso f B).hom =
      (actionChosenUnitComponentIso f A).hom ≫
        chosenToActionMap f (actionToChosenMap f a) := sorry

/-- The unit isomorphism of the action/chosen-descent equivalence. -/
noncomputable def actionChosenUnitIso {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y) :
    𝟭 (GroupoidScheme.Action
        (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)) ≅
      actionToChosen f ⋙ chosenToAction f :=
  NatIso.ofComponents (actionChosenUnitComponentIso f)
    (actionChosenUnit_naturality f)

/-- The component comparison for the chosen-descent roundtrip. -/
noncomputable def chosenCounitComponentIso {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) (i : PUnit.{1}) :
    (actionToChosenObj f (chosenToActionObj f D)).obj i ≅ D.obj i :=
  let G := GroupoidScheme.pullback (GroupoidScheme.discrete Y) f
  let eU := G.U.iteratedSliceEquiv
  match i with
  | ⟨⟩ => eU.counitIso.app (D.obj PUnit.unit)

/-- The chosen-descent counit components commute with the pairwise comparisons. -/
theorem chosenCounitComponentIso_comm {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    ∀ i j : PUnit.{1},
      (Scheme.overPseudofunctor.map (cechPair f).p₁.op.toLoc).toFunctor.map
            (chosenCounitComponentIso f D i).hom ≫
          D.hom i j =
        (actionToChosenObj f (chosenToActionObj f D)).hom i j ≫
          (Scheme.overPseudofunctor.map (cechPair f).p₂.op.toLoc).toFunctor.map
            (chosenCounitComponentIso f D j).hom := sorry

/-- The chosen-descent-to-action-to-descent counit component. -/
noncomputable def chosenCounitIso {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (D : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)) :
    actionToChosenObj f (chosenToActionObj f D) ≅ D :=
  Pseudofunctor.DescentData'.isoMk (chosenCounitComponentIso f D)
    (chosenCounitComponentIso_comm f D)

/-- The chosen-descent counit components are natural. -/
theorem chosenCounitIso_naturality {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    {D E : Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
      (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
      (fun _ _ _ ↦ cechTriple f)} (a : D ⟶ E) :
    actionToChosenMap f (chosenToActionMap f a) ≫ (chosenCounitIso f E).hom =
      (chosenCounitIso f D).hom ≫ a := sorry

/-- The counit isomorphism of the action/chosen-descent equivalence. -/
noncomputable def actionChosenCounitIso {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y) :
    chosenToAction f ⋙ actionToChosen f ≅
      𝟭 (Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
        (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
        (fun _ _ _ ↦ cechTriple f)) :=
  NatIso.ofComponents (chosenCounitIso f) (chosenCounitIso_naturality f)

/-- The explicit action/chosen-descent unit and counit satisfy the triangle law. -/
theorem actionChosen_triangle {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) :
    ∀ A,
      (actionToChosen f).map ((actionChosenUnitIso f).hom.app A) ≫
          (actionChosenCounitIso f).hom.app ((actionToChosen f).obj A) =
        𝟙 ((actionToChosen f).obj A) := sorry

/-- The concrete equivalence between Čech-groupoid actions and chosen descent data. -/
noncomputable def actionChosenEquivalence {S : Scheme.{u}}
    {X Y : Over S} (f : X ⟶ Y) :
    GroupoidScheme.Action (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f) ≌
      Scheme.DescentData.Chosen (fun _ : PUnit.{1} ↦ X.left)
        (fun _ : PUnit.{1} ↦ f.left) (fun _ _ ↦ cechPair f)
        (fun _ _ _ ↦ cechTriple f) where
  functor := actionToChosen f
  inverse := chosenToAction f
  unitIso := actionChosenUnitIso f
  counitIso := actionChosenCounitIso f
  functor_unitIso_comp := actionChosen_triangle f

/-- Groupoid schemes cartesian over the Čech groupoid `pullback (discrete Y) f` are
equivalent to scheme descent data relative to `X/Y`. -/
noncomputable def descentEquivalence {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    GroupoidScheme.CartesianOver
        (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f) ≌
      Scheme.DescentData (fun _ : PUnit.{1} ↦ X.left)
        (fun _ : PUnit.{1} ↦ f.left) :=
  (cartesianActionEquivalence
      (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)).trans
    ((actionChosenEquivalence f).trans
      (Chosen.equivalence
        (fun _ : PUnit.{1} ↦ X.left) (fun _ : PUnit.{1} ↦ f.left)
        (fun _ _ ↦ cechPair f) (fun _ _ _ ↦ cechTriple f)))

/-- The forward functor of `descentEquivalence` is the explicit composite through groupoid
actions and the chosen-pullback presentation of descent data. -/
theorem descentEquivalence_functor {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    (descentEquivalence f).functor =
      (cartesianActionEquivalence
          (GroupoidScheme.pullback (GroupoidScheme.discrete Y) f)).functor ⋙
        (actionChosenEquivalence f).functor ⋙
          (Chosen.equivalence
            (fun _ : PUnit.{1} ↦ X.left) (fun _ : PUnit.{1} ↦ f.left)
            (fun _ _ ↦ cechPair f) (fun _ _ _ ↦ cechTriple f)).functor := sorry

end AlgebraicGeometry.GroupoidScheme.CartesianOver
