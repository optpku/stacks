/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Basic
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Cartesian
public import ReasLib.CategoryTheory.Fibered.CategoryOver.CartesianHom
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback on morphisms of fibred categories

This leaf owns the total, based, and bundled `1`-cell action of pullback along a fixed base
functor.
-/

@[expose] public section

noncomputable section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pullback

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- The categorical commutative square defining pullback of a morphism of fibred categories.
Its first leg is unchanged and its second leg applies the supplied total functor. -/
noncomputable def square
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    CategoricalPullback.CatCommSqOver u Y.p (CategoricalPullback u X.p) where
  fst := CategoricalPullback.π₁ u X.p
  snd := CategoricalPullback.π₂ u X.p ⋙ FiberedCategoryOver.toFunctor F
  iso := (CategoricalPullback.catCommSq u X.p).iso ≪≫
    Functor.isoWhiskerLeft (CategoricalPullback.π₂ u X.p)
      (FiberedCategoryOver.toBasedFunctor F).projectionIso.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The total-category functor induced by pulling back a morphism of fibred categories. -/
noncomputable def totalMap
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    CategoricalPullback u X.p ⥤ CategoricalPullback u Y.p :=
  (square u F).comparison

/-- Pullback on total categories retains the object in the base category. -/
@[simp]
theorem totalMap.obj.fst
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y)
    (x : CategoricalPullback u X.p) :
    ((totalMap u F).obj x).fst = x.fst := sorry

/-- Pullback on total categories applies the supplied functor to the second object. -/
@[simp]
theorem totalMap.obj.snd
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y)
    (x : CategoricalPullback u X.p) :
    ((totalMap u F).obj x).snd = (FiberedCategoryOver.toFunctor F).obj x.snd := sorry

/-- Pullback on total categories retains the first component of a morphism. -/
@[simp]
theorem totalMap.map.fst
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y)
    {x y : CategoricalPullback u X.p} (f : x ⟶ y) :
    ((totalMap u F).map f).fst = f.fst := sorry

/-- Pullback on total categories applies the supplied functor to the second component of a
morphism. -/
@[simp]
theorem totalMap.map.snd
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y)
    {x y : CategoricalPullback u X.p} (f : x ⟶ y) :
    ((totalMap u F).map f).snd = (FiberedCategoryOver.toFunctor F).map f.snd := sorry

/-- The total pullback map commutes strictly with the first projections to `C`. -/
theorem totalMap.compProjection
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    totalMap u F ⋙ CategoricalPullback.π₁ u Y.p =
      CategoricalPullback.π₁ u X.p := sorry

/-- Pullback of the underlying based functor along `u`. -/
noncomputable def basedMap
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    (FiberedCategoryOver.pullback u X).toBasedCategory ⥤ᵇ
      (FiberedCategoryOver.pullback u Y).toBasedCategory :=
  BasedFunctor.ofFunctor (totalMap u F) (totalMap.compProjection u F)

/-- The based pullback map preserves strongly cartesian arrows. -/
theorem basedMap.preservesStronglyCartesian
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    (basedMap u F).PreservesStronglyCartesian := sorry

/-- Pullback of a morphism of fibred categories along the fixed base functor `u`. -/
@[stacks 04WE "pullback of a cartesian functor"]
noncomputable def mapCanonical
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    FiberedCategoryOver.pullback u X ⟶ FiberedCategoryOver.pullback u Y :=
  FiberedCategoryOver.ofBasedFunctor
    (basedMap u F) (basedMap.preservesStronglyCartesian u F)

/-- Forgetting the bundled pullback map recovers the based pullback map. -/
@[simp]
theorem mapCanonical.toBasedFunctor
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (mapCanonical u F) = basedMap u F := sorry

/-- The total functor of the bundled pullback map is the categorical-pullback comparison. -/
@[simp]
theorem mapCanonical.toFunctor
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (mapCanonical u F) = totalMap u F := sorry

end FiberedCategoryOver.Pullback

end CategoryTheory
