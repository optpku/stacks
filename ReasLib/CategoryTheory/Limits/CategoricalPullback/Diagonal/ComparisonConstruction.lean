/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic

/-!
# Construction of the categorical-pullback diagonal comparison

This leaf owns the private square coherence and the resulting ordinary comparison functor.
Projection formulas and the explicit inverse are kept in the corresponding computation and
equivalence leaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

open Functor

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace CategoricalPullback

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The top composite in the diagonal comparison square.

It first postcomposes both pullback legs by `H`, then maps the resulting pullback to the
diagonal self-pullback `H ⊡ H`. -/
private def squareTop
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ H ⊡ H :=
  postcompose F G H ⋙ toDiagonal F G H

/-- The bottom composite in the diagonal comparison square.

It remembers the common `C`-object via `toBase F G` and then applies `Δₚ H`. -/
private def squareBottom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ H ⊡ H :=
  toBase F G ⋙ diagonal H

/-- Compatibility for the objectwise component of the diagonal-square comparison. -/
private theorem squareComponent_fac
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    H.map (𝟙 (F.obj X.fst)) ≫
        ((squareBottom F G H).obj X).iso.hom =
      ((squareTop F G H).obj X).iso.hom ≫ H.map X.iso.inv := sorry

/-- The objectwise component of the diagonal-square comparison is identity on the first
projection and `X.iso.symm` on the second. -/
private noncomputable def squareComponentIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (squareTop F G H).obj X ≅ (squareBottom F G H).obj X :=
  CategoricalPullback.mkIso (.refl _) X.iso.symm
    (squareComponent_fac F G H X)

/-- The objectwise diagonal-square components are natural. -/
private theorem squareComponentIso_naturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : F ⊡ G} (f : X ⟶ Y) :
    (squareTop F G H).map f ≫ (squareComponentIso F G H Y).hom =
      (squareComponentIso F G H X).hom ≫ (squareBottom F G H).map f := sorry

/-- The displayed diagonal square is `2`-commutative. -/
private noncomputable def squareIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    squareTop F G H ≅ squareBottom F G H :=
  NatIso.ofComponents (squareComponentIso F G H)
    (squareComponentIso_naturality F G H)

end Implementation

/-- The canonical diagonal square over `toDiagonal F G H` and `Δₚ H`.

Its top route is common-base postcomposition and its bottom route remembers the common base
object before applying the relative diagonal. -/
noncomputable def diagonalSquareOver
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    CatCommSqOver (toDiagonal F G H) (diagonal H) (F ⊡ G) :=
  { fst := postcompose F G H
    snd := toBase F G
    iso := Implementation.squareIso F G H }

/-- The canonical comparison from `F ⊡ G` to the pullback of `toDiagonal F G H` and `Δₚ H`. -/
noncomputable def diagonalComparison
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ (toDiagonal F G H) ⊡ (diagonal H) :=
  (diagonalSquareOver F G H).comparison

end CategoricalPullback

end CategoryTheory.Limits
