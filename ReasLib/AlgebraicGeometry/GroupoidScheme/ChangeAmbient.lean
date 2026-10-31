/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# Changing the ambient scheme of a groupoid scheme

This module retains the object and arrow schemes of a groupoid over a new ambient scheme
whenever the source and target maps have the same composite to that scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The object scheme of a groupoid after retaining its objects over a new ambient base. -/
abbrev changeAmbientU {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : Over S :=
  Over.mk q

/-- The arrow scheme of a groupoid after retaining its source map over a new ambient base. -/
abbrev changeAmbientR {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : Over S :=
  Over.mk (H.s.left ≫ q)

/-- The retained source map over a new ambient base. -/
def changeAmbientSource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : changeAmbientR H q ⟶ changeAmbientU H q :=
  Over.homMk H.s.left

/-- The retained target map is a morphism over the new ambient base. -/
theorem changeAmbientTarget_condition {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    H.t.left ≫ q = (changeAmbientR H q).hom := h

/-- The retained target map over a new ambient base. -/
def changeAmbientTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientR H q ⟶ changeAmbientU H q :=
  Over.homMk H.t.left (changeAmbientTarget_condition H q h)

/-- The underlying comparison between the two ambient-base presentations of composable arrows. -/
def changeAmbientComposable {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    (pullback (changeAmbientSource H q) (changeAmbientTarget H q h)).left ⟶
      (pullback H.s H.t).left :=
  (PreservesPullback.iso (Over.forget S) (changeAmbientSource H q)
      (changeAmbientTarget H q h)).hom ≫
    (PreservesPullback.iso (Over.forget T) H.s H.t).inv

private theorem changeAmbientComposable_fst {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientComposable H q h ≫ (pullback.fst H.s H.t).left =
      (pullback.fst (changeAmbientSource H q) (changeAmbientTarget H q h)).left := by
  dsimp only [changeAmbientComposable]
  erw [Category.assoc, PreservesPullback.iso_inv_fst]
  exact PreservesPullback.iso_hom_fst (Over.forget S) (changeAmbientSource H q)
    (changeAmbientTarget H q h)

private theorem changeAmbientComposable_snd {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientComposable H q h ≫ (pullback.snd H.s H.t).left =
      (pullback.snd (changeAmbientSource H q) (changeAmbientTarget H q h)).left := by
  dsimp only [changeAmbientComposable]
  erw [Category.assoc, PreservesPullback.iso_inv_snd]
  exact PreservesPullback.iso_hom_snd (Over.forget S) (changeAmbientSource H q)
    (changeAmbientTarget H q h)

/-- Retained composition respects the new ambient structure map. -/
theorem changeAmbientComposition_condition {S T : Scheme.{u}}
    (H : GroupoidScheme T) (q : H.U.left ⟶ S)
    (h : H.t.left ≫ q = H.s.left ≫ q) :
    (changeAmbientComposable H q h ≫ H.c.left) ≫ (changeAmbientR H q).hom =
      (pullback (changeAmbientSource H q) (changeAmbientTarget H q h)).hom := by
  calc
    (changeAmbientComposable H q h ≫ H.c.left) ≫ (changeAmbientR H q).hom =
        (changeAmbientComposable H q h ≫ (H.c ≫ H.s).left) ≫ q := by
      simp only [Over.mk_hom, Over.comp_left, Category.assoc]
    _ = ((changeAmbientComposable H q h ≫ (pullback.snd H.s H.t).left) ≫
        H.s.left) ≫ q := by
      rw [H.comp_source]
      simp only [Over.comp_left, Category.assoc]
    _ = (pullback.snd (changeAmbientSource H q) (changeAmbientTarget H q h)).left ≫
        (changeAmbientR H q).hom := by
      rw [changeAmbientComposable_snd]
      simp only [Over.mk_hom, Category.assoc]
      rfl
    _ = _ := Over.w _

/-- The retained composition map over a new ambient base. -/
def changeAmbientComposition {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    pullback (changeAmbientSource H q) (changeAmbientTarget H q h) ⟶
      changeAmbientR H q :=
  Over.homMk (changeAmbientComposable H q h ≫ H.c.left)
    (changeAmbientComposition_condition H q h)

-- The comparison identifies lifts with the same two underlying arrows. The domain over
-- the old base is supplied explicitly, since a point over the new base need not lie over it.
set_option backward.isDefEq.respectTransparency false in
private theorem changeAmbientComposition_left {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) {X : Over S}
    (r : X.left ⟶ T) (a b : X ⟶ changeAmbientR H q)
    (a' b' : Over.mk r ⟶ H.R) (ha : a'.left = a.left) (hb : b'.left = b.left)
    (hab : a ≫ changeAmbientSource H q = b ≫ changeAmbientTarget H q h)
    (hab' : a' ≫ H.s = b' ≫ H.t) :
    (pullback.lift a b hab ≫ changeAmbientComposition H q h).left =
      (pullback.lift a' b' hab' ≫ H.c).left := by
  have hlift : (pullback.lift a b hab).left ≫ changeAmbientComposable H q h =
      (pullback.lift a' b' hab').left := by
    apply (cancel_mono (PreservesPullback.iso (Over.forget T) H.s H.t).hom).1
    simp only [changeAmbientComposable, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    change (Over.forget S).map (pullback.lift a b hab) ≫
        (PreservesPullback.iso (Over.forget S) (changeAmbientSource H q)
          (changeAmbientTarget H q h)).hom =
      (Over.forget T).map (pullback.lift a' b' hab') ≫
        (PreservesPullback.iso (Over.forget T) H.s H.t).hom
    simp only [PreservesPullback.iso_hom]
    erw [map_lift_pullbackComparison, map_lift_pullbackComparison]
    simp only [Over.forget_map, ha, hb, changeAmbientSource, changeAmbientTarget]
    rfl
  change (pullback.lift a b hab).left ≫ (changeAmbientComposable H q h ≫ H.c.left) =
    (pullback.lift a' b' hab').left ≫ H.c.left
  rw [← Category.assoc, hlift]

/-- Retained identity arrows respect the new ambient structure map. -/
theorem changeAmbientIdentity_condition {S T : Scheme.{u}}
    (H : GroupoidScheme T) (q : H.U.left ⟶ S) :
    H.e.left ≫ (changeAmbientR H q).hom = (changeAmbientU H q).hom := by
  change H.e.left ≫ H.s.left ≫ q = q
  rw [← Category.assoc, ← Over.comp_left, H.identity_source, Over.id_left,
    Category.id_comp]

/-- The retained identity map over a new ambient base. -/
def changeAmbientIdentity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : changeAmbientU H q ⟶ changeAmbientR H q :=
  Over.homMk H.e.left (changeAmbientIdentity_condition H q)

/-- Retained inverse arrows respect the new ambient structure map. -/
theorem changeAmbientInverse_condition {S T : Scheme.{u}}
    (H : GroupoidScheme T) (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    H.i.left ≫ (changeAmbientR H q).hom = (changeAmbientR H q).hom := by
  simp only [Over.mk_hom]
  rw [← Category.assoc, ← Over.comp_left, H.inverse_source, h]

/-- The retained inverse map over a new ambient base. -/
def changeAmbientInverse {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientR H q ⟶ changeAmbientR H q :=
  Over.homMk H.i.left (changeAmbientInverse_condition H q h)

/-- Retained composition has the source of its second arrow. -/
theorem changeAmbient_compSource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientComposition H q h ≫ changeAmbientSource H q =
      pullback.snd (changeAmbientSource H q) (changeAmbientTarget H q h) ≫
        changeAmbientSource H q := by
  apply Over.OverMorphism.ext
  change (changeAmbientComposable H q h ≫ H.c.left) ≫ H.s.left =
    (pullback.snd (changeAmbientSource H q) (changeAmbientTarget H q h)).left ≫ H.s.left
  rw [Category.assoc, ← Over.comp_left, H.comp_source, Over.comp_left,
    ← Category.assoc, changeAmbientComposable_snd]
  rfl

/-- Retained composition has the target of its first arrow. -/
theorem changeAmbient_compTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientComposition H q h ≫ changeAmbientTarget H q h =
      pullback.fst (changeAmbientSource H q) (changeAmbientTarget H q h) ≫
        changeAmbientTarget H q h := by
  apply Over.OverMorphism.ext
  change (changeAmbientComposable H q h ≫ H.c.left) ≫ H.t.left =
    (pullback.fst (changeAmbientSource H q) (changeAmbientTarget H q h)).left ≫ H.t.left
  rw [Category.assoc, ← Over.comp_left, H.comp_target, Over.comp_left,
    ← Category.assoc, changeAmbientComposable_fst]
  rfl

/-- Retained identity arrows have the specified source. -/
theorem changeAmbient_identitySource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) :
    changeAmbientIdentity H q ≫ changeAmbientSource H q = 𝟙 (changeAmbientU H q) := by
  apply Over.OverMorphism.ext
  change H.e.left ≫ H.s.left = 𝟙 H.U.left
  exact congrArg (fun f : H.U ⟶ H.U => f.left) H.identity_source

/-- Retained identity arrows have the specified target. -/
theorem changeAmbient_identityTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientIdentity H q ≫ changeAmbientTarget H q h = 𝟙 (changeAmbientU H q) := by
  apply Over.OverMorphism.ext
  change H.e.left ≫ H.t.left = 𝟙 H.U.left
  exact congrArg (fun f : H.U ⟶ H.U => f.left) H.identity_target

/-- Retained inversion exchanges source and target. -/
theorem changeAmbient_inverseSource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientInverse H q h ≫ changeAmbientSource H q = changeAmbientTarget H q h := by
  apply Over.OverMorphism.ext
  change H.i.left ≫ H.s.left = H.t.left
  exact congrArg (fun f : H.R ⟶ H.U => f.left) H.inverse_source

/-- Retained inversion exchanges target and source. -/
theorem changeAmbient_inverseTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientInverse H q h ≫ changeAmbientTarget H q h = changeAmbientSource H q := by
  apply Over.OverMorphism.ext
  change H.i.left ≫ H.t.left = H.s.left
  exact congrArg (fun f : H.R ⟶ H.U => f.left) H.inverse_target

-- Composable arrows have the same structure map to the old ambient scheme.
private theorem changeAmbient_base_eq {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) {X : Over S}
    (a b : X ⟶ changeAmbientR H q)
    (hab : a ≫ changeAmbientSource H q = b ≫ changeAmbientTarget H q h) :
    a.left ≫ H.R.hom = b.left ≫ H.R.hom := by
  have hab' : a.left ≫ H.s.left = b.left ≫ H.t.left :=
    congrArg (fun f : X ⟶ changeAmbientU H q => f.left) hab
  calc
    a.left ≫ H.R.hom = (a.left ≫ H.s.left) ≫ H.U.hom := by
      erw [Category.assoc, Over.w]
    _ = (b.left ≫ H.t.left) ≫ H.U.hom := by rw [hab']
    _ = b.left ≫ H.R.hom := by erw [Category.assoc, Over.w]

/-- Retained composition is associative on points over the new ambient base. -/
theorem changeAmbient_associativity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a b d : X ⟶ changeAmbientR H q)
      (h_ab : a ≫ changeAmbientSource H q = b ≫ changeAmbientTarget H q h)
      (h_bd : b ≫ changeAmbientSource H q = d ≫ changeAmbientTarget H q h)
      (h_ab_d : (pullback.lift a b h_ab ≫ changeAmbientComposition H q h) ≫
        changeAmbientSource H q = d ≫ changeAmbientTarget H q h)
      (h_a_bd : a ≫ changeAmbientSource H q =
        (pullback.lift b d h_bd ≫ changeAmbientComposition H q h) ≫
          changeAmbientTarget H q h),
      pullback.lift (pullback.lift a b h_ab ≫ changeAmbientComposition H q h) d h_ab_d ≫
          changeAmbientComposition H q h =
        pullback.lift a (pullback.lift b d h_bd ≫ changeAmbientComposition H q h) h_a_bd ≫
          changeAmbientComposition H q h := by
  intro X a b d h_ab h_bd h_ab_d h_a_bd
  let r := a.left ≫ H.R.hom
  let a' : Over.mk r ⟶ H.R := Over.homMk a.left
  let b' : Over.mk r ⟶ H.R :=
    Over.homMk b.left (changeAmbient_base_eq H q h a b h_ab).symm
  let d' : Over.mk r ⟶ H.R := Over.homMk d.left
    ((changeAmbient_base_eq H q h b d h_bd).symm.trans
      (changeAmbient_base_eq H q h a b h_ab).symm)
  have hab' : a' ≫ H.s = b' ≫ H.t := by
    apply Over.OverMorphism.ext
    change a.left ≫ H.s.left = b.left ≫ H.t.left
    exact congrArg (fun f : X ⟶ changeAmbientU H q => f.left) h_ab
  have hbd' : b' ≫ H.s = d' ≫ H.t := by
    apply Over.OverMorphism.ext
    change b.left ≫ H.s.left = d.left ≫ H.t.left
    exact congrArg (fun f : X ⟶ changeAmbientU H q => f.left) h_bd
  have hab_d' : (pullback.lift a' b' hab' ≫ H.c) ≫ H.s = d' ≫ H.t := by
    simpa only [Category.assoc, H.comp_source, pullback.lift_snd_assoc] using hbd'
  have ha_bd' : a' ≫ H.s = (pullback.lift b' d' hbd' ≫ H.c) ≫ H.t := by
    simpa only [Category.assoc, H.comp_target, pullback.lift_fst_assoc] using hab'
  have hc_ab := changeAmbientComposition_left H q h r a b a' b' rfl rfl h_ab hab'
  have hc_bd := changeAmbientComposition_left H q h r b d b' d' rfl rfl h_bd hbd'
  have hleft := changeAmbientComposition_left H q h r
    (pullback.lift a b h_ab ≫ changeAmbientComposition H q h) d
    (pullback.lift a' b' hab' ≫ H.c) d' hc_ab.symm rfl h_ab_d hab_d'
  have hright := changeAmbientComposition_left H q h r a
    (pullback.lift b d h_bd ≫ changeAmbientComposition H q h) a'
    (pullback.lift b' d' hbd' ≫ H.c) rfl hc_bd.symm h_a_bd ha_bd'
  apply Over.OverMorphism.ext
  exact hleft.trans ((congrArg (fun f : Over.mk r ⟶ H.R => f.left)
    (H.associativity a' b' d' hab' hbd' hab_d' ha_bd')).trans hright.symm)

/-- Retained composition has the right identity law. -/
theorem changeAmbient_rightIdentity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : a ≫ changeAmbientSource H q =
        ((a ≫ changeAmbientSource H q) ≫ changeAmbientIdentity H q) ≫
          changeAmbientTarget H q h),
      pullback.lift a ((a ≫ changeAmbientSource H q) ≫ changeAmbientIdentity H q) ha ≫
        changeAmbientComposition H q h = a := by
  intro X a ha
  let a' : Over.mk (a.left ≫ H.R.hom) ⟶ H.R := Over.homMk a.left
  have ha' : a' ≫ H.s = ((a' ≫ H.s) ≫ H.e) ≫ H.t := by
    simp [Category.assoc, H.identity_target]
  apply Over.OverMorphism.ext
  exact (changeAmbientComposition_left H q h _ a _ a' ((a' ≫ H.s) ≫ H.e)
    rfl rfl ha ha').trans
      (congrArg (fun f : Over.mk (a.left ≫ H.R.hom) ⟶ H.R => f.left)
        (H.right_identity a' ha'))

/-- Retained composition has the left identity law. -/
theorem changeAmbient_leftIdentity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : ((a ≫ changeAmbientTarget H q h) ≫ changeAmbientIdentity H q) ≫
          changeAmbientSource H q = a ≫ changeAmbientTarget H q h),
      pullback.lift ((a ≫ changeAmbientTarget H q h) ≫ changeAmbientIdentity H q) a ha ≫
        changeAmbientComposition H q h = a := by
  intro X a ha
  let a' : Over.mk (a.left ≫ H.R.hom) ⟶ H.R := Over.homMk a.left
  have ha' : ((a' ≫ H.t) ≫ H.e) ≫ H.s = a' ≫ H.t := by
    simp [Category.assoc, H.identity_source]
  apply Over.OverMorphism.ext
  exact (changeAmbientComposition_left H q h _ _ a ((a' ≫ H.t) ≫ H.e) a'
    rfl rfl ha ha').trans
      (congrArg (fun f : Over.mk (a.left ≫ H.R.hom) ⟶ H.R => f.left)
        (H.left_identity a' ha'))

/-- Retained composition of an arrow with its inverse is its target identity. -/
theorem changeAmbient_inverseComp {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : a ≫ changeAmbientSource H q =
        (a ≫ changeAmbientInverse H q h) ≫ changeAmbientTarget H q h),
      pullback.lift a (a ≫ changeAmbientInverse H q h) ha ≫
          changeAmbientComposition H q h =
        (a ≫ changeAmbientTarget H q h) ≫ changeAmbientIdentity H q := by
  intro X a ha
  let a' : Over.mk (a.left ≫ H.R.hom) ⟶ H.R := Over.homMk a.left
  have ha' : a' ≫ H.s = (a' ≫ H.i) ≫ H.t := by
    simp [Category.assoc, H.inverse_target]
  apply Over.OverMorphism.ext
  exact (changeAmbientComposition_left H q h _ a _ a' (a' ≫ H.i)
    rfl rfl ha ha').trans
      (congrArg (fun f : Over.mk (a.left ≫ H.R.hom) ⟶ H.R => f.left)
        (H.inverse_comp a' ha'))

/-- Retained composition of an inverse with its arrow is its source identity. -/
theorem changeAmbient_compInverse {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : (a ≫ changeAmbientInverse H q h) ≫ changeAmbientSource H q =
        a ≫ changeAmbientTarget H q h),
      pullback.lift (a ≫ changeAmbientInverse H q h) a ha ≫
          changeAmbientComposition H q h =
        (a ≫ changeAmbientSource H q) ≫ changeAmbientIdentity H q := by
  intro X a ha
  let a' : Over.mk (a.left ≫ H.R.hom) ⟶ H.R := Over.homMk a.left
  have ha' : (a' ≫ H.i) ≫ H.s = a' ≫ H.t := by
    simp [Category.assoc, H.inverse_source]
  apply Over.OverMorphism.ext
  exact (changeAmbientComposition_left H q h _ _ a (a' ≫ H.i) a'
    rfl rfl ha ha').trans
      (congrArg (fun f : Over.mk (a.left ≫ H.R.hom) ⟶ H.R => f.left)
        (H.comp_inverse a' ha'))

/-- Retain a groupoid's object and arrow schemes over a new ambient base when source and target
have the same composite to that base. -/
def changeAmbient {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) : GroupoidScheme S where
  U := changeAmbientU H q
  R := changeAmbientR H q
  s := changeAmbientSource H q
  t := changeAmbientTarget H q h
  c := changeAmbientComposition H q h
  e := changeAmbientIdentity H q
  i := changeAmbientInverse H q h
  comp_source := changeAmbient_compSource H q h
  comp_target := changeAmbient_compTarget H q h
  identity_source := changeAmbient_identitySource H q
  identity_target := changeAmbient_identityTarget H q h
  inverse_source := changeAmbient_inverseSource H q h
  inverse_target := changeAmbient_inverseTarget H q h
  associativity := changeAmbient_associativity H q h
  right_identity := changeAmbient_rightIdentity H q h
  left_identity := changeAmbient_leftIdentity H q h
  inverse_comp := changeAmbient_inverseComp H q h
  comp_inverse := changeAmbient_compInverse H q h


end AlgebraicGeometry.GroupoidScheme
