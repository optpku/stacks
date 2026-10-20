/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Comparison

/-!
# Readouts for the categorical-pullback diagonal comparison

This leaf contains projection, object, morphism, and structural-isomorphism formulas for
`CategoricalPullback.diagonalComparison`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback.DiagonalComparison

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

variable (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)

/-- The two component isomorphisms defining the structural comparison satisfy compatibility. -/
theorem obj.iso.fac (X : F ⊡ G) :
    H.map (𝟙 (F.obj X.fst)) ≫ ((Δₚ H).obj (F.obj X.fst)).iso.hom =
      ((toDiagonal F G H).obj ((postcompose F G H).obj X)).iso.hom ≫
        H.map X.iso.inv := sorry

/-- The structural isomorphism of the comparison is identity on the first coordinate and
`X.iso.symm` on the second. -/
@[simp] theorem obj.iso (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).iso =
      CategoricalPullback.mkIso
        (x := (toDiagonal F G H).obj ((diagonalComparison F G H).obj X).fst)
        (y := (Δₚ H).obj ((diagonalComparison F G H).obj X).snd)
        (Iso.refl _) X.iso.symm (obj.iso.fac F G H X) := sorry

/-- The forward structural morphism of the comparison is the explicit componentwise map. -/
@[simp] theorem obj.iso.hom (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).iso.hom =
      (CategoricalPullback.mkIso
        (x := (toDiagonal F G H).obj ((diagonalComparison F G H).obj X).fst)
        (y := (Δₚ H).obj ((diagonalComparison F G H).obj X).snd)
        (Iso.refl _) X.iso.symm (obj.iso.fac F G H X)).hom := sorry

/-- The inverse structural morphism of the comparison is the explicit inverse component. -/
@[simp] theorem obj.iso.inv (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).iso.inv =
      (CategoricalPullback.mkIso
        (x := (toDiagonal F G H).obj ((diagonalComparison F G H).obj X).fst)
        (y := (Δₚ H).obj ((diagonalComparison F G H).obj X).snd)
        (Iso.refl _) X.iso.symm (obj.iso.fac F G H X)).inv := sorry

/-- The forward comparison is the identity on the outer-left projection. -/
@[simp] theorem obj.iso.hom.fst (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).iso.hom.fst = 𝟙 (F.obj X.fst) := sorry

/-- The forward comparison records `X.iso.inv` on the outer-right projection. -/
@[simp] theorem obj.iso.hom.snd (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).iso.hom.snd = X.iso.inv := sorry

/-- The inverse comparison is the identity on the outer-left projection. -/
@[simp] theorem obj.iso.inv.fst (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).iso.inv.fst = 𝟙 (F.obj X.fst) := sorry

/-- The inverse comparison records `X.iso.hom` on the outer-right projection. -/
@[simp] theorem obj.iso.inv.snd (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).iso.inv.snd = X.iso.hom := sorry

/-- The first endpoint of the comparison retains the original left object. -/
@[simp] theorem obj.fstFst (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).fst.fst = X.fst := sorry

/-- The second coordinate of the first endpoint retains the original right object. -/
@[simp] theorem obj.fstSnd (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).fst.snd = X.snd := sorry

/-- The second endpoint is the image of the original left object. -/
@[simp] theorem obj.snd (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).snd = F.obj X.fst := sorry

/-- The structural isomorphism on the first endpoint is the image of `X.iso`. -/
@[simp] theorem obj.fstIso (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).fst.iso = H.mapIso X.iso := sorry

/-- The forward structural map on the first endpoint is `H.map X.iso.hom`. -/
@[simp] theorem obj.fstIso.hom (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).fst.iso.hom = H.map X.iso.hom := sorry

/-- The inverse structural map on the first endpoint is `H.map X.iso.inv`. -/
@[simp] theorem obj.fstIso.inv (X : F ⊡ G) :
    ((diagonalComparison F G H).obj X).fst.iso.inv = H.map X.iso.inv := sorry

/-- The first morphism component of the comparison retains `f.fst`. -/
@[simp] theorem map.fstFst {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((diagonalComparison F G H).map f).fst.fst = f.fst := sorry

/-- The second morphism component of the first endpoint retains `f.snd`. -/
@[simp] theorem map.fstSnd {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((diagonalComparison F G H).map f).fst.snd = f.snd := sorry

/-- The second endpoint morphism is `F.map f.fst`. -/
@[simp] theorem map.snd {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((diagonalComparison F G H).map f).snd = F.map f.fst := sorry

/-- The forward component of the upper projection comparison is an identity. -/
@[simp] theorem fstIso.hom.app (X : F ⊡ G) :
    (fstIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the upper projection comparison is an identity. -/
@[simp] theorem fstIso.inv.app (X : F ⊡ G) :
    (fstIso F G H).inv.app X = 𝟙 _ := sorry

/-- The forward component of the lower projection comparison is an identity. -/
@[simp] theorem sndIso.hom.app (X : F ⊡ G) :
    (sndIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the lower projection comparison is an identity. -/
@[simp] theorem sndIso.inv.app (X : F ⊡ G) :
    (sndIso F G H).inv.app X = 𝟙 _ := sorry

end CategoryTheory.Limits.CategoricalPullback.DiagonalComparison
