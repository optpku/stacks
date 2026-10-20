module

public import ReasLib.CategoryTheory.Fibered.RestrictionComparison

/-! Restriction comparisons of fibre categories along commuting squares. -/

@[expose] public section

open CategoryTheory Limits CategoricalPullback Functor
open scoped CategoricalPullback

universe v₁ v₂ u₁ u₂

#check (CategoryTheory.Functor.restrictionSquare :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY),
    CatCommSqOver (Chosen.reindex p toY) (Chosen.reindex p toX') (p.Fiber Y'))

#check (CategoryTheory.Functor.restrictionSquare_fst :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY),
    (restrictionSquare p hw).fst = Chosen.reindex p fromY)

#check (CategoryTheory.Functor.restrictionSquare_snd :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY),
    (restrictionSquare p hw).snd = Chosen.reindex p fromX')

#check (CategoryTheory.Functor.restrictionComparison :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY),
    p.Fiber Y' ⥤ (Chosen.reindex p toY) ⊡ (Chosen.reindex p toX'))

#check (CategoryTheory.Functor.restrictionComparison_obj_fst :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y'),
    ((restrictionComparison p hw).obj y).fst = (Chosen.reindex p fromY).obj y)

#check (CategoryTheory.Functor.restrictionComparison_obj_snd :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y'),
    ((restrictionComparison p hw).obj y).snd = (Chosen.reindex p fromX').obj y)

#check (CategoryTheory.Functor.restrictionComparison_obj_iso :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y'),
    ((restrictionComparison p hw).obj y).iso = (restrictionSquare p hw).iso.app y)

#check (CategoryTheory.Functor.restrictionComparison_spec :
  ∀ {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
    (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y'),
    ((restrictionComparison p hw).obj y).fst = (Chosen.reindex p fromY).obj y ∧
      ((restrictionComparison p hw).obj y).snd = (Chosen.reindex p fromX').obj y ∧
      ((restrictionComparison p hw).obj y).iso =
        (restrictionSquare p hw).iso.app y)
