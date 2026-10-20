/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Bicategory.StrictPseudofunctor.Inverse
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfBase.OverSlice

/-!
# Change-of-base constructions for algebraic stacks

Construction A views an algebraic stack over `S` as an algebraic stack over `S'`
by postcomposing the projection with `Over.map g`, and records the original
projection as a morphism to `overSlice g`. Construction B recovers an algebraic
stack over `S` from such a pair by taking the structural total functor and
transporting along `Over.iteratedSliceForward`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Postcomposition `Over.map g` along a morphism of schemes is fibred in
groupoids. -/
instance overMap_isFiberedInGroupoids {S S' : Scheme.{u}} (g : S ⟶ S') :
    Functor.IsFibered.InGroupoids (Over.map g) :=
  sorry

/-- The forward functor of `Over.iteratedSliceEquiv (Over.mk g)` is fibred in
groupoids. -/
instance iteratedSliceForward_isFiberedInGroupoids {S S' : Scheme.{u}}
    (g : S ⟶ S') :
    Functor.IsFibered.InGroupoids (Over.iteratedSliceForward (Over.mk g)) :=
  sorry

namespace AlgebraicStack

/-- Construction A on groupoid fibrations: the same total category, with
projection postcomposed by `Over.map g`. -/
def viewedOver {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S) :
    GroupoidsOver S' :=
  Groupoids.comp X (Over.map g)

/-- Construction A does not change the total category. -/
@[simp]
theorem viewedOver_total {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S) :
    (viewedOver g X).total = X.total :=
  sorry

/-- The projection of `viewedOver g X` is `X.p` followed by `Over.map g`. -/
@[simp]
theorem viewedOver_p {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S) :
    (viewedOver g X).p = X.p ⋙ Over.map g :=
  sorry

/-- Construction A preserves algebraic stacks. -/
instance viewedOver.algebraicStack {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : GroupoidsOver S) [AlgebraicStack X] :
    AlgebraicStack (viewedOver g X) :=
  sorry

/-- The structural based functor of Construction A, landing in the canonical
slice of `S` over `S'`. -/
theorem viewedOverHom_w {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S) :
    (X.p ⋙ Over.iteratedSliceBackward (Over.mk g)) ⋙
        (GroupoidsOver.slice (Over.mk g)).p =
      (viewedOver g X).p :=
  sorry

/-- The structural 1-morphism `viewedOver g X ⟶ (Sch/S)_fppf` over `S'`, whose
total functor is the original projection transported along
`Over.iteratedSliceBackward`. -/
def viewedOverHom {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S) :
    viewedOver g X ⟶ GroupoidsOver.slice (Over.mk g) :=
  Groupoids.ofBasedFunctor
    { toFunctor := X.p ⋙ Over.iteratedSliceBackward (Over.mk g)
      w := viewedOverHom_w g X }

/-- The total functor of `viewedOverHom g X` is the original projection followed
by `Over.iteratedSliceBackward`. -/
@[simp]
theorem viewedOverHom_toFunctor {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : GroupoidsOver S) :
    Groupoids.toFunctor (viewedOverHom g X) =
      X.p ⋙ Over.iteratedSliceBackward (Over.mk g) :=
  sorry

/-- A 1-morphism of groupoid fibrations over `S` commutes with the postcomposed
projections to `Over S'`. -/
theorem viewedOverMap_w {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : GroupoidsOver S} (F : X ⟶ Y) :
    (Groupoids.toFunctor F : X.total ⥤ Y.total) ⋙ (viewedOver g Y).p =
      (viewedOver g X).p :=
  sorry

/-- Construction A on 1-morphisms: the same total functor, now over `S'`. -/
def viewedOverMap {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : GroupoidsOver S}
    (F : X ⟶ Y) : viewedOver g X ⟶ viewedOver g Y :=
  Groupoids.ofBasedFunctor
    { toFunctor := (Groupoids.toFunctor F : X.total ⥤ Y.total)
      w := viewedOverMap_w g F }

/-- The total functor of `viewedOverMap g F` is the original total functor. -/
@[simp]
theorem viewedOverMap_toFunctor {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : GroupoidsOver S} (F : X ⟶ Y) :
    Groupoids.toFunctor (viewedOverMap g F) =
      (Groupoids.toFunctor F : X.total ⥤ Y.total) :=
  sorry

/-- Construction A on 2-morphisms: the same total natural transformation. -/
def viewedOverMap₂ {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : GroupoidsOver S}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    viewedOverMap g F ⟶ viewedOverMap g H :=
  Groupoids.ofBasedNatTrans
    { toNatTrans :=
        (Groupoids.toNatTrans eta :
          (Groupoids.toFunctor F : X.total ⥤ Y.total) ⟶
            (Groupoids.toFunctor H : X.total ⥤ Y.total))
      isHomLift' := fun a ↦ by
        have transport : ∀ {b c : Y.total} {R T : Over S} (f : R ⟶ T) (φ : b ⟶ c),
            Y.p.IsHomLift f φ →
              (Y.p ⋙ Over.map g).IsHomLift ((Over.map g).map f) φ := by
          intro b c R T f φ h
          cases h
          exact .map φ
        change Functor.IsHomLift (Y.p ⋙ Over.map g)
          (𝟙 ((Over.map g).obj (X.p.obj a))) ((Groupoids.toNatTrans eta).app a)
        have ht := transport _ _ ((Groupoids.toBasedNatTrans eta).isHomLift' a)
        rw [(Over.map g).map_id] at ht
        exact ht }

end AlgebraicStack

namespace AlgebraicStacks

open AlgebraicStack

/-- Lift a morphism of underlying groupoid fibrations to a 1-morphism of
algebraic stacks. -/
private abbrev ofHom {S : Scheme.{u}} {X Y : AlgebraicStacks S}
    (F : toGroupoids X ⟶ toGroupoids Y) : X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom F

/-- Lift a 2-morphism of underlying groupoid fibrations to a 2-morphism of
algebraic stacks. -/
private abbrev ofHom₂ {S : Scheme.{u}} {X Y : AlgebraicStacks S} {F G : X ⟶ Y}
    (eta : F.hom ⟶ G.hom) : F ⟶ G :=
  Bicategory.InducedBicategory.Hom₂.mk eta

/-- Construction A on objects of `AlgebraicStacks S`. -/
def toOverSliceObj {S S' : Scheme.{u}} (g : S ⟶ S') (X : AlgebraicStacks S) :
    OverSlice g :=
  OverSlice.mk (of (viewedOver g (toGroupoids X)))
    (ofHom (viewedOverHom g (toGroupoids X)))

/-- The domain of Construction A is the algebraic stack `viewedOver g X`. -/
@[simp]
theorem toOverSliceObj_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : AlgebraicStacks S) :
    (toOverSliceObj g X).obj = of (viewedOver g (toGroupoids X)) :=
  sorry

/-- Construction A does not change the total category of an algebraic stack. -/
theorem toOverSliceObj_total {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : AlgebraicStacks S) :
    (toGroupoids (toOverSliceObj g X).obj).total = (toGroupoids X).total :=
  sorry

/-- The ambient 1-morphism of Construction A on a morphism of algebraic stacks
commutes with the structural morphisms to `overSlice g`. -/
theorem toOverSliceMap_comm {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : AlgebraicStacks S} (F : X ⟶ Y) :
    ofHom (viewedOverMap g F.hom) ≫ (toOverSliceObj g Y).hom =
      (toOverSliceObj g X).hom :=
  sorry

/-- Construction A on 1-morphisms of algebraic stacks. -/
def toOverSliceMap {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : AlgebraicStacks S}
    (F : X ⟶ Y) : toOverSliceObj g X ⟶ toOverSliceObj g Y :=
  Bicategory.StrictSlice.Hom.mk (ofHom (viewedOverMap g F.hom))
    (toOverSliceMap_comm g F)

/-- The ambient 2-morphism of Construction A is compatible with the strict-slice
triangles. -/
theorem toOverSliceMap₂_comm {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : AlgebraicStacks S} {F H : X ⟶ Y} (eta : F ⟶ H) :
    ofHom₂ (viewedOverMap₂ g eta.hom) ▷ (toOverSliceObj g Y).hom ≫
        eqToHom (Bicategory.StrictSlice.Hom.comm (toOverSliceMap g H)) =
      eqToHom (Bicategory.StrictSlice.Hom.comm (toOverSliceMap g F)) :=
  sorry

/-- Construction A on 2-morphisms of algebraic stacks. -/
def toOverSliceMap₂ {S S' : Scheme.{u}} (g : S ⟶ S') {X Y : AlgebraicStacks S}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    toOverSliceMap g F ⟶ toOverSliceMap g H :=
  Bicategory.StrictSlice.Hom₂.mk (ofHom₂ (viewedOverMap₂ g eta.hom))
    (toOverSliceMap₂_comm g eta)

/-- Construction A preserves identity 1-morphisms. -/
theorem toOverSliceMap_id {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : AlgebraicStacks S) :
    toOverSliceMap g (𝟙 X) = 𝟙 (toOverSliceObj g X) :=
  sorry

/-- Construction A preserves composition of 1-morphisms. -/
theorem toOverSliceMap_comp {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y Z : AlgebraicStacks S} (F : X ⟶ Y) (H : Y ⟶ Z) :
    toOverSliceMap g (F ≫ H) = toOverSliceMap g F ≫ toOverSliceMap g H :=
  sorry

/-- Construction A preserves identity 2-morphisms. -/
theorem toOverSliceMap₂_id {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : AlgebraicStacks S} (F : X ⟶ Y) :
    toOverSliceMap₂ g (𝟙 F) = 𝟙 (toOverSliceMap g F) :=
  sorry

/-- Construction A preserves vertical composition of 2-morphisms. -/
theorem toOverSliceMap₂_comp {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : AlgebraicStacks S} {F H K : X ⟶ Y} (eta : F ⟶ H) (theta : H ⟶ K) :
    toOverSliceMap₂ g (eta ≫ theta) =
      toOverSliceMap₂ g eta ≫ toOverSliceMap₂ g theta :=
  sorry

/-- Construction A is compatible with left whiskering. -/
theorem toOverSliceMap₂_whiskerLeft {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y Z : AlgebraicStacks S} (F : X ⟶ Y) {H K : Y ⟶ Z} (eta : H ⟶ K) :
    toOverSliceMap₂ g (F ◁ eta) =
      eqToHom (toOverSliceMap_comp g F H) ≫
        toOverSliceMap g F ◁ toOverSliceMap₂ g eta ≫
          eqToHom (toOverSliceMap_comp g F K).symm :=
  sorry

/-- Construction A is compatible with right whiskering. -/
theorem toOverSliceMap₂_whiskerRight {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y Z : AlgebraicStacks S} {F H : X ⟶ Y} (eta : F ⟶ H) (K : Y ⟶ Z) :
    toOverSliceMap₂ g (eta ▷ K) =
      eqToHom (toOverSliceMap_comp g F K) ≫
        toOverSliceMap₂ g eta ▷ toOverSliceMap g K ≫
          eqToHom (toOverSliceMap_comp g H K).symm :=
  sorry

/-- The strict-pseudofunctor data of Construction A. -/
private def toOverSliceCore {S S' : Scheme.{u}} (g : S ⟶ S') :
    StrictPseudofunctorPreCore (AlgebraicStacks S) (OverSlice g) where
  obj := toOverSliceObj g
  map := toOverSliceMap g
  map₂ := toOverSliceMap₂ g
  map_id := toOverSliceMap_id g
  map_comp := toOverSliceMap_comp g
  map₂_id := toOverSliceMap₂_id g
  map₂_comp := toOverSliceMap₂_comp g
  map₂_whisker_left := toOverSliceMap₂_whiskerLeft g
  map₂_whisker_right := toOverSliceMap₂_whiskerRight g

/-- Construction A: the strict pseudofunctor sending an algebraic stack over `S`
to the pair consisting of the same stack viewed over `S'` and its structural
morphism to `overSlice g`. -/
def toOverSlice {S S' : Scheme.{u}} (g : S ⟶ S') :
    StrictPseudofunctor (AlgebraicStacks S) (OverSlice g) :=
  StrictPseudofunctor.mk'' (toOverSliceCore g)

/-- The object action of `toOverSlice g` is `toOverSliceObj g`. -/
@[simp]
theorem toOverSlice_obj {S S' : Scheme.{u}} (g : S ⟶ S') (X : AlgebraicStacks S) :
    (toOverSlice g).obj X = toOverSliceObj g X :=
  sorry

/-- The morphism action of `toOverSlice g` is `toOverSliceMap g`. -/
@[simp]
theorem toOverSlice_map {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : AlgebraicStacks S} (F : X ⟶ Y) :
    (toOverSlice g).map F = toOverSliceMap g F :=
  sorry

/-- The restricted projection of a pair, as a functor to `Over S`. -/
def ofOverSliceProjection {S S' : Scheme.{u}} (g : S ⟶ S') (P : OverSlice g) :
    (toGroupoids P.obj).total ⥤ Over S :=
  Groupoids.toFunctor P.hom.hom ⋙ Over.iteratedSliceForward (Over.mk g)

/-- The restricted projection of a pair is fibred in groupoids over `Over S`. -/
instance ofOverSliceProjection.isFiberedInGroupoids {S S' : Scheme.{u}}
    (g : S ⟶ S') (P : OverSlice g) :
    Functor.IsFibered.InGroupoids (ofOverSliceProjection g P) :=
  sorry

/-- Construction B on the underlying groupoid fibration of a pair: the
structural total functor, transported along `Over.iteratedSliceForward`. -/
def ofOverSliceGroupoids {S S' : Scheme.{u}} (g : S ⟶ S') (P : OverSlice g) :
    GroupoidsOver S :=
  Groupoids.ofFunctor (ofOverSliceProjection g P)

/-- Construction B does not change the total category of the domain algebraic
stack. -/
@[simp]
theorem ofOverSliceGroupoids_total {S S' : Scheme.{u}} (g : S ⟶ S')
    (P : OverSlice g) :
    (ofOverSliceGroupoids g P).total = (toGroupoids P.obj).total :=
  sorry

/-- The projection of Construction B is the structural total functor followed by
`Over.iteratedSliceForward`. -/
@[simp]
theorem ofOverSliceGroupoids_p {S S' : Scheme.{u}} (g : S ⟶ S')
    (P : OverSlice g) :
    (ofOverSliceGroupoids g P).p = ofOverSliceProjection g P :=
  sorry

/-- Construction B preserves algebraic stacks. -/
instance ofOverSliceGroupoids.algebraicStack {S S' : Scheme.{u}} (g : S ⟶ S')
    (P : OverSlice g) : AlgebraicStack (ofOverSliceGroupoids g P) :=
  sorry

/-- Construction B on objects of the pair 2-category. -/
abbrev ofOverSliceObj {S S' : Scheme.{u}} (g : S ⟶ S') (P : OverSlice g) :
    AlgebraicStacks S :=
  of (ofOverSliceGroupoids g P)

/-- Construction B on objects is `AlgebraicStacks.of` of the restricted groupoid
fibration. -/
@[simp]
theorem ofOverSliceObj_eq {S S' : Scheme.{u}} (g : S ⟶ S') (P : OverSlice g) :
    ofOverSliceObj g P = of (ofOverSliceGroupoids g P) :=
  sorry

/-- Lift a restricted 1-morphism to a 1-morphism of algebraic stacks over `S`. -/
abbrev ofOverSliceHom {S S' : Scheme.{u}} (g : S ⟶ S') {P Q : OverSlice g}
    (F : ofOverSliceGroupoids g P ⟶ ofOverSliceGroupoids g Q) :
    ofOverSliceObj g P ⟶ ofOverSliceObj g Q :=
  ofHom F

/-- Lift a restricted 2-morphism to a 2-morphism of algebraic stacks over `S`. -/
abbrev ofOverSliceHom₂ {S S' : Scheme.{u}} (g : S ⟶ S') {P Q : OverSlice g}
    {F H : ofOverSliceGroupoids g P ⟶ ofOverSliceGroupoids g Q} (eta : F ⟶ H) :
    ofOverSliceHom g F ⟶ ofOverSliceHom g H :=
  ofHom₂ eta

/-- A morphism of pairs commutes with the restricted projections to `Over S`. -/
theorem ofOverSliceMap_w {S S' : Scheme.{u}} (g : S ⟶ S') {P Q : OverSlice g}
    (F : P ⟶ Q) :
    (Groupoids.toFunctor (Bicategory.StrictSlice.Hom.hom F).hom :
          (toGroupoids P.obj).total ⥤ (toGroupoids Q.obj).total) ⋙
        (ofOverSliceGroupoids g Q).p =
      (ofOverSliceGroupoids g P).p :=
  sorry

/-- Construction B on 1-morphisms of pairs. -/
def ofOverSliceMap {S S' : Scheme.{u}} (g : S ⟶ S') {P Q : OverSlice g}
    (F : P ⟶ Q) : ofOverSliceGroupoids g P ⟶ ofOverSliceGroupoids g Q :=
  Groupoids.ofBasedFunctor
    { toFunctor :=
        (Groupoids.toFunctor (Bicategory.StrictSlice.Hom.hom F).hom :
          (toGroupoids P.obj).total ⥤ (toGroupoids Q.obj).total)
      w := ofOverSliceMap_w g F }

/-- Construction B on 2-morphisms of pairs. -/
def ofOverSliceMap₂ {S S' : Scheme.{u}} (g : S ⟶ S') {P Q : OverSlice g}
    {F H : P ⟶ Q} (eta : F ⟶ H) : ofOverSliceMap g F ⟶ ofOverSliceMap g H :=
  Groupoids.ofBasedNatTrans
    { toNatTrans :=
        (Groupoids.toNatTrans (Bicategory.StrictSlice.Hom₂.hom eta).hom :
          (Groupoids.toFunctor (Bicategory.StrictSlice.Hom.hom F).hom :
              (toGroupoids P.obj).total ⥤ (toGroupoids Q.obj).total) ⟶
            (Groupoids.toFunctor (Bicategory.StrictSlice.Hom.hom H).hom :
              (toGroupoids P.obj).total ⥤ (toGroupoids Q.obj).total))
      isHomLift' := fun a ↦ by
        have restrictLift
            (p : (toGroupoids Q.obj).total ⥤ Over S')
            (q : (toGroupoids Q.obj).total ⥤ Over S)
            (w : q ⋙ Over.forget S = p ⋙ Over.forget S')
            {b c : (toGroupoids Q.obj).total} (φ : b ⟶ c)
            (R : Over S) (U : Over S') (hb : q.obj b = R) (hc : q.obj c = R)
            (h : p.IsHomLift (𝟙 U) φ) (e : R.left = U.left) :
            q.IsHomLift (𝟙 R) φ := by
          have transport : ∀ {b c : (toGroupoids Q.obj).total} {U V : Over S'}
              (f : U ⟶ V) (φ : b ⟶ c), p.IsHomLift f φ →
                (p ⋙ Over.forget S').IsHomLift ((Over.forget S').map f) φ := by
            intro b c U V f φ h
            cases h
            exact .map φ
          have hbase := transport _ _ h
          change (p ⋙ Over.forget S').IsHomLift (𝟙 U.left) φ at hbase
          rw [← w, ← e] at hbase
          apply IsHomLift.of_fac q _ _ hb hc
          apply Over.OverMorphism.ext
          have fac := @IsHomLift.fac _ _ _ _ (q ⋙ Over.forget S) _ _ _ _ _ _ hbase
          simp only [Functor.comp_map, Over.forget_map, Over.id_left, Over.comp_left,
            Over.eqToHom_left] at fac ⊢
          exact fac
        exact restrictLift (toGroupoids Q.obj).p (ofOverSliceGroupoids g Q).p
          (congrArg (fun F ↦ F ⋙ Over.forget S') (Groupoids.comm Q.hom.hom))
          ((Groupoids.toNatTrans (Bicategory.StrictSlice.Hom₂.hom eta).hom).app a)
          ((ofOverSliceGroupoids g P).p.obj a) ((toGroupoids P.obj).p.obj a)
          (BasedFunctor.w_obj (Groupoids.toBasedFunctor (ofOverSliceMap g F)) a)
          (BasedFunctor.w_obj (Groupoids.toBasedFunctor (ofOverSliceMap g H)) a)
          ((Groupoids.toBasedNatTrans (Bicategory.StrictSlice.Hom₂.hom eta).hom).isHomLift' a)
          (congrArg (fun F ↦ (F.obj a).left) (Groupoids.comm P.hom.hom)) }

/-- Construction B preserves identity 1-morphisms. -/
theorem ofOverSliceMap_id {S S' : Scheme.{u}} (g : S ⟶ S') (P : OverSlice g) :
    (ofOverSliceHom g (ofOverSliceMap g (𝟙 P)) : ofOverSliceObj g P ⟶ ofOverSliceObj g P) =
      𝟙 (ofOverSliceObj g P) :=
  sorry

/-- Construction B preserves composition of 1-morphisms. -/
theorem ofOverSliceMap_comp {S S' : Scheme.{u}} (g : S ⟶ S')
    {P Q R : OverSlice g} (F : P ⟶ Q) (H : Q ⟶ R) :
    (ofOverSliceHom g (ofOverSliceMap g (F ≫ H)) :
        ofOverSliceObj g P ⟶ ofOverSliceObj g R) =
      (ofOverSliceHom g (ofOverSliceMap g F) : ofOverSliceObj g P ⟶ ofOverSliceObj g Q) ≫
        (ofOverSliceHom g (ofOverSliceMap g H) : ofOverSliceObj g Q ⟶ ofOverSliceObj g R) :=
  sorry

/-- Construction B preserves identity 2-morphisms. -/
theorem ofOverSliceMap₂_id {S S' : Scheme.{u}} (g : S ⟶ S') {P Q : OverSlice g}
    (F : P ⟶ Q) :
    (ofOverSliceHom₂ g (ofOverSliceMap₂ g (𝟙 F)) :
        ofOverSliceHom g (ofOverSliceMap g F) ⟶ ofOverSliceHom g (ofOverSliceMap g F)) =
      𝟙 (ofOverSliceHom g (ofOverSliceMap g F) :
          ofOverSliceObj g P ⟶ ofOverSliceObj g Q) :=
  sorry

/-- Construction B preserves vertical composition of 2-morphisms. -/
theorem ofOverSliceMap₂_comp {S S' : Scheme.{u}} (g : S ⟶ S')
    {P Q : OverSlice g} {F H K : P ⟶ Q} (eta : F ⟶ H) (theta : H ⟶ K) :
    (ofOverSliceHom₂ g (ofOverSliceMap₂ g (eta ≫ theta)) :
        ofOverSliceHom g (ofOverSliceMap g F) ⟶ ofOverSliceHom g (ofOverSliceMap g K)) =
      (ofOverSliceHom₂ g (ofOverSliceMap₂ g eta) :
          ofOverSliceHom g (ofOverSliceMap g F) ⟶ ofOverSliceHom g (ofOverSliceMap g H)) ≫
        (ofOverSliceHom₂ g (ofOverSliceMap₂ g theta) :
          ofOverSliceHom g (ofOverSliceMap g H) ⟶ ofOverSliceHom g (ofOverSliceMap g K)) :=
  sorry

/-- Construction B is compatible with left whiskering. -/
theorem ofOverSliceMap₂_whiskerLeft {S S' : Scheme.{u}} (g : S ⟶ S')
    {P Q R : OverSlice g} (F : P ⟶ Q) {H K : Q ⟶ R} (eta : H ⟶ K) :
    (ofOverSliceHom₂ g (ofOverSliceMap₂ g (F ◁ eta)) :
        ofOverSliceHom g (ofOverSliceMap g (F ≫ H)) ⟶ ofOverSliceHom g (ofOverSliceMap g (F ≫ K))) =
      eqToHom (ofOverSliceMap_comp g F H) ≫
        (ofOverSliceHom g (ofOverSliceMap g F) :
              ofOverSliceObj g P ⟶ ofOverSliceObj g Q) ◁
            (ofOverSliceHom₂ g (ofOverSliceMap₂ g eta) :
              ofOverSliceHom g (ofOverSliceMap g H) ⟶ ofOverSliceHom g (ofOverSliceMap g K)) ≫
          eqToHom (ofOverSliceMap_comp g F K).symm :=
  sorry

/-- Construction B is compatible with right whiskering. -/
theorem ofOverSliceMap₂_whiskerRight {S S' : Scheme.{u}} (g : S ⟶ S')
    {P Q R : OverSlice g} {F H : P ⟶ Q} (eta : F ⟶ H) (K : Q ⟶ R) :
    (ofOverSliceHom₂ g (ofOverSliceMap₂ g (eta ▷ K)) :
        ofOverSliceHom g (ofOverSliceMap g (F ≫ K)) ⟶ ofOverSliceHom g (ofOverSliceMap g (H ≫ K))) =
      eqToHom (ofOverSliceMap_comp g F K) ≫
        (ofOverSliceHom₂ g (ofOverSliceMap₂ g eta) :
              ofOverSliceHom g (ofOverSliceMap g F) ⟶ ofOverSliceHom g (ofOverSliceMap g H)) ▷
            (ofOverSliceHom g (ofOverSliceMap g K) :
              ofOverSliceObj g Q ⟶ ofOverSliceObj g R) ≫
          eqToHom (ofOverSliceMap_comp g H K).symm :=
  sorry

/-- The strict-pseudofunctor data of Construction B. -/
private def ofOverSliceCore {S S' : Scheme.{u}} (g : S ⟶ S') :
    StrictPseudofunctorPreCore (OverSlice g) (AlgebraicStacks S) where
  obj := ofOverSliceObj g
  map := fun F ↦ ofOverSliceHom g (ofOverSliceMap g F)
  map₂ := fun eta ↦ ofOverSliceHom₂ g (ofOverSliceMap₂ g eta)
  map_id := ofOverSliceMap_id g
  map_comp := ofOverSliceMap_comp g
  map₂_id := ofOverSliceMap₂_id g
  map₂_comp := ofOverSliceMap₂_comp g
  map₂_whisker_left := ofOverSliceMap₂_whiskerLeft g
  map₂_whisker_right := ofOverSliceMap₂_whiskerRight g

/-- Construction B: the strict pseudofunctor sending a pair `(X', f)` to the
algebraic stack over `S` with the same total category and projection the
structural total functor of `f`, transported along
`Over.iteratedSliceForward`. -/
def ofOverSlice {S S' : Scheme.{u}} (g : S ⟶ S') :
    StrictPseudofunctor (OverSlice g) (AlgebraicStacks S) :=
  StrictPseudofunctor.mk'' (ofOverSliceCore g)

/-- The object action of `ofOverSlice g` is `ofOverSliceObj g`. -/
@[simp]
theorem ofOverSlice_obj {S S' : Scheme.{u}} (g : S ⟶ S') (P : OverSlice g) :
    (ofOverSlice g).obj P = ofOverSliceObj g P :=
  sorry

/-- Viewing an algebraic stack over the larger base and restricting the resulting pair
are mutually inverse strict pseudofunctors. -/
theorem toOverSlice.isStrictInverse {S S' : Scheme.{u}} (g : S ⟶ S') :
    StrictPseudofunctor.IsStrictInverse (toOverSlice g) (ofOverSlice g) :=
  sorry

/-- Construction A is a biequivalence of 2-categories. -/
instance toOverSlice.isBiequivalence {S S' : Scheme.{u}} (g : S ⟶ S') :
    Pseudofunctor.IsBiequivalence (toOverSlice g).toPseudofunctor :=
  sorry

/-- Construction B is a biequivalence of 2-categories. -/
instance ofOverSlice.isBiequivalence {S S' : Scheme.{u}} (g : S ⟶ S') :
    Pseudofunctor.IsBiequivalence (ofOverSlice g).toPseudofunctor :=
  sorry

end AlgebraicStacks

end AlgebraicGeometry

