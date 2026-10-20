/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Categorical commutative squares as pseudopullback cones

This module is the bridge between mathlib's ordinary-category presentation
`CatCommSqOver F G X` and the bicategorical walking-cospan presentation in `Cat`.

It contains only the interpretation of squares, its field computations, and its functoriality.
The explicit categorical pullback comparison belongs to `CategoricalPullback.CatCommSqOver`;
bilimit criteria and selected pullback models belong to higher modules.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Limits.CategoricalPullback.CatCommSqOver

variable {X : Type u} [Category.{v} X]
variable {A : Type u} [Category.{v} A]
variable {B : Type u} [Category.{v} B]
variable {C : Type u} [Category.{v} C]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- A categorical commutative square over `F` and `G`, viewed as the readable
pseudopullback-cone presentation in the bicategory `Cat`. -/
def toPseudoPullbackCone (P : CatCommSqOver F G X) :
    Bicategory.PseudoPullbackCone F.toCatHom G.toCatHom where
  pt := Cat.of X
  fst := P.fst.toCatHom
  snd := P.snd.toCatHom
  iso := Cat.Hom.isoMk P.iso

/-- The apex of the pseudopullback cone associated to a categorical commutative square. -/
@[simp]
theorem toPseudoPullbackCone.pt (P : CatCommSqOver F G X) :
    P.toPseudoPullbackCone.pt = Cat.of X := sorry

/-- The left projection of the pseudopullback cone associated to a categorical commutative
square. -/
@[simp]
theorem toPseudoPullbackCone.fst (P : CatCommSqOver F G X) :
    P.toPseudoPullbackCone.fst = P.fst.toCatHom := sorry

/-- The right projection of the pseudopullback cone associated to a categorical commutative
square. -/
@[simp]
theorem toPseudoPullbackCone.snd (P : CatCommSqOver F G X) :
    P.toPseudoPullbackCone.snd = P.snd.toCatHom := sorry

/-- The comparison isomorphism of the pseudopullback cone associated to a categorical
commutative square. -/
@[simp]
theorem toPseudoPullbackCone.iso (P : CatCommSqOver F G X) :
    P.toPseudoPullbackCone.iso = Cat.Hom.isoMk P.iso := sorry

/-- The bilimit predicate for a categorical commutative square regarded as a pseudopullback
cone in `Cat`.

This is only a presentation-level abbreviation. The universal property remains the neutral
Yoneda condition owned by `Bicategory.PseudoCone.IsBilimit`. -/
abbrev IsBilimit (P : CatCommSqOver F G X) : Prop :=
  P.toPseudoPullbackCone.IsBilimit

namespace Implementation

/-- The components used internally to interpret a morphism of categorical commutative squares
as a modification between the corresponding walking-cospan pseudocones. -/
private def toPseudoConeMapApp {P Q : CatCommSqOver F G X} (η : P ⟶ Q) :
    (j : LocallyDiscrete Limits.WalkingCospan) →
      P.toPseudoPullbackCone.toPseudoCone.π.app j ⟶
        Q.toPseudoPullbackCone.toPseudoCone.π.app j
  | ⟨Limits.WalkingCospan.one⟩ => (Functor.whiskerRight η.fst F).toCatHom₂
  | ⟨Limits.WalkingCospan.left⟩ => η.fst.toCatHom₂
  | ⟨Limits.WalkingCospan.right⟩ => η.snd.toCatHom₂

/-- The components of `toPseudoConeMapApp η` satisfy modification naturality. -/
private theorem toPseudoConeMapApp_naturality {P Q : CatCommSqOver F G X} (η : P ⟶ Q) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) (Cat.of X)).map h ◁
          toPseudoConeMapApp η b ≫ (Q.toPseudoPullbackCone.toPseudoCone.π.naturality h).hom =
        (P.toPseudoPullbackCone.toPseudoCone.π.naturality h).hom ≫
          toPseudoConeMapApp η a ▷
            (Bicategory.cospan F.toCatHom G.toCatHom).map h := sorry

/-- A morphism of categorical commutative squares, viewed as a modification between the
corresponding walking-cospan pseudocones. -/
private def toPseudoConeMap (P Q : CatCommSqOver F G X) (η : P ⟶ Q) :
    P.toPseudoPullbackCone.toPseudoCone.π ⟶ Q.toPseudoPullbackCone.toPseudoCone.π where
  as.app := toPseudoConeMapApp η
  as.naturality := toPseudoConeMapApp_naturality η

/-- Passing a categorical commutative-square morphism to a modification preserves identities. -/
private theorem toPseudoConeMap_id (P : CatCommSqOver F G X) :
    toPseudoConeMap P P (𝟙 P) = 𝟙 P.toPseudoPullbackCone.toPseudoCone.π := sorry

/-- Passing categorical commutative-square morphisms to modifications preserves composition. -/
private theorem toPseudoConeMap_comp {P Q R : CatCommSqOver F G X}
    (η : P ⟶ Q) (θ : Q ⟶ R) :
    toPseudoConeMap P R (η ≫ θ) =
      toPseudoConeMap P Q η ≫ toPseudoConeMap Q R θ := sorry

end Implementation

/-- Categorical commutative squares over `F` and `G`, functorially interpreted as strong
transformations from the constant diagram at `X` to the walking-cospan diagram. -/
def toPseudoConeFunctor (X : Type u) [Category.{v} X] (F : A ⥤ C) (G : B ⥤ C) :
    CatCommSqOver F G X ⥤
      (Pseudofunctor.const (LocallyDiscrete Limits.WalkingCospan) (Cat.of X) ⟶
        Bicategory.cospan F.toCatHom G.toCatHom) where
  obj P := P.toPseudoPullbackCone.toPseudoCone.π
  map {P Q} η := Implementation.toPseudoConeMap P Q η
  map_id := Implementation.toPseudoConeMap_id
  map_comp := Implementation.toPseudoConeMap_comp

/-- On objects, `toPseudoConeFunctor` is the generic pseudocone represented by the readable
pseudopullback square. -/
@[simp]
theorem toPseudoConeFunctor.obj (P : CatCommSqOver F G X) :
    (toPseudoConeFunctor X F G).obj P = P.toPseudoPullbackCone.toPseudoCone.π := sorry

/-- On a square morphism, the left-vertex component is its first natural transformation. -/
@[simp]
theorem toPseudoConeFunctor.map.app.left {P Q : CatCommSqOver F G X} (η : P ⟶ Q) :
    ((toPseudoConeFunctor X F G).map η).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      η.fst.toCatHom₂ := sorry

/-- On a square morphism, the right-vertex component is its second natural transformation. -/
@[simp]
theorem toPseudoConeFunctor.map.app.right {P Q : CatCommSqOver F G X} (η : P ⟶ Q) :
    ((toPseudoConeFunctor X F G).map η).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      η.snd.toCatHom₂ := sorry

/-- On a square morphism, the central component is its first natural transformation whiskered
by the left cospan leg. -/
@[simp]
theorem toPseudoConeFunctor.map.app.one {P Q : CatCommSqOver F G X} (η : P ⟶ Q) :
    ((toPseudoConeFunctor X F G).map η).as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      (Functor.whiskerRight η.fst F).toCatHom₂ := sorry

/-- Interpreting categorical commutative squares as walking-cospan strong transformations is
an equivalence of categories. -/
instance toPseudoConeFunctor.isEquivalence :
    (toPseudoConeFunctor X F G).IsEquivalence := sorry

/- Data audit (mathlib 4.32): `toPseudoPullbackCone` reports only `propext`,
`Classical.choice`, and `Quot.sound`. `toPseudoConeFunctor` additionally reports `sorryAx`,
confined to the Prop-valued modification naturality and functor identity/composition laws; its
object and component data are the explicit constructions above. -/

end Limits.CategoricalPullback.CatCommSqOver

end CategoryTheory
