/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic

/-!
# Readouts for the cospan-to-diagonal action

This leaf gives computation formulas for `CategoricalPullback.toDiagonal` and its two projection
comparisons.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

variable (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)

/-- `toDiagonal` applies `F` to the left endpoint object. -/
@[simp] theorem toDiagonal.obj.fst (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((toDiagonal F G H).obj X).fst = F.obj X.fst := sorry

/-- `toDiagonal` applies `G` to the right endpoint object. -/
@[simp] theorem toDiagonal.obj.snd (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((toDiagonal F G H).obj X).snd = G.obj X.snd := sorry

/-- `toDiagonal` retains the pullback structural isomorphism. -/
@[simp] theorem toDiagonal.obj.iso (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((toDiagonal F G H).obj X).iso = X.iso := sorry

/-- `toDiagonal` applies `F` to the left morphism component. -/
@[simp] theorem toDiagonal.hom.fst {X Y : (F ⋙ H) ⊡ (G ⋙ H)} (f : X ⟶ Y) :
    ((toDiagonal F G H).map f).fst = F.map f.fst := sorry

/-- `toDiagonal` applies `G` to the right morphism component. -/
@[simp] theorem toDiagonal.hom.snd {X Y : (F ⋙ H) ⊡ (G ⋙ H)} (f : X ⟶ Y) :
    ((toDiagonal F G H).map f).snd = G.map f.snd := sorry

/-- The forward structural map of `toDiagonal` is the original forward map. -/
@[simp] theorem toDiagonal.obj.iso.hom (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((toDiagonal F G H).obj X).iso.hom = X.iso.hom := sorry

/-- The inverse structural map of `toDiagonal` is the original inverse map. -/
@[simp] theorem toDiagonal.obj.iso.inv (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((toDiagonal F G H).obj X).iso.inv = X.iso.inv := sorry

/-- The forward component of the first projection comparison for `toDiagonal`. -/
@[simp] theorem toDiagonalFstIso.hom.app (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    (toDiagonalFstIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the first projection comparison for `toDiagonal`. -/
@[simp] theorem toDiagonalFstIso.inv.app (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    (toDiagonalFstIso F G H).inv.app X = 𝟙 _ := sorry

/-- The forward component of the second projection comparison for `toDiagonal`. -/
@[simp] theorem toDiagonalSndIso.hom.app (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    (toDiagonalSndIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the second projection comparison for `toDiagonal`. -/
@[simp] theorem toDiagonalSndIso.inv.app (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    (toDiagonalSndIso F G H).inv.app X = 𝟙 _ := sorry

end CategoryTheory.Limits.CategoricalPullback
