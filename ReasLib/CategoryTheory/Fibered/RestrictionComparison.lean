module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Restriction comparison of fibre categories along a commuting square

A cleavage of a fibred functor turns a commuting square in the base into a 2-commutative
square of fibre categories. The induced functor into the 2-fibre product is
`restrictionComparison`.
-/

@[expose] public section

open CategoryTheory Limits CategoricalPullback
open scoped CategoricalPullback

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace CategoryTheory.Functor

/-- The 2-commutative square of fibre categories obtained by restricting along a
commuting square in the base. -/
noncomputable def restrictionSquare (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    CatCommSqOver (Chosen.reindex p toY) (Chosen.reindex p toX') (p.Fiber Y') where
  fst := Chosen.reindex p fromY
  snd := Chosen.reindex p fromX'
  iso :=
    (Chosen.Reindex.compIso p fromY toY).symm ≪≫
      Chosen.Reindex.congrIso p hw.symm ≪≫
      Chosen.Reindex.compIso p fromX' toX'

/-- The first leg of `restrictionSquare` is reindexing along `fromY`. -/
@[simp]
theorem restrictionSquare_fst (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    (restrictionSquare p hw).fst = Chosen.reindex p fromY := sorry

/-- The second leg of `restrictionSquare` is reindexing along `fromX'`. -/
@[simp]
theorem restrictionSquare_snd (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    (restrictionSquare p hw).snd = Chosen.reindex p fromX' := sorry

/-- The comparison functor from `p.Fiber Y'` into the 2-fibre product of the
restrictions along `X ⟶ Y` and `X ⟶ X'`. -/
noncomputable def restrictionComparison (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    p.Fiber Y' ⥤ (Chosen.reindex p toY) ⊡ (Chosen.reindex p toX') :=
  (restrictionSquare p hw).comparison

/-- The first projection of `restrictionComparison` on objects is reindexing along `fromY`. -/
@[simp]
theorem restrictionComparison_obj_fst (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y') :
    ((restrictionComparison p hw).obj y).fst = (Chosen.reindex p fromY).obj y := sorry

/-- The second projection of `restrictionComparison` on objects is reindexing along `fromX'`. -/
@[simp]
theorem restrictionComparison_obj_snd (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y') :
    ((restrictionComparison p hw).obj y).snd = (Chosen.reindex p fromX').obj y := sorry

/-- The structural isomorphism of `restrictionComparison` on objects is the square's 2-cell. -/
@[simp]
theorem restrictionComparison_obj_iso (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y') :
    ((restrictionComparison p hw).obj y).iso = (restrictionSquare p hw).iso.app y := sorry

/-- Objects of `restrictionComparison` record the two restrictions and the structural 2-cell. -/
theorem restrictionComparison_spec (p : S ⥤ C) [p.IsFibered]
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) (y : p.Fiber Y') :
    ((restrictionComparison p hw).obj y).fst = (Chosen.reindex p fromY).obj y ∧
      ((restrictionComparison p hw).obj y).snd = (Chosen.reindex p fromX').obj y ∧
      ((restrictionComparison p hw).obj y).iso =
        (restrictionSquare p hw).iso.app y := sorry

end CategoryTheory.Functor

