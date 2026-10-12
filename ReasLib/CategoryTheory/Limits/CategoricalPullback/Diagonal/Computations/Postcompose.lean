/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic

/-!
# Readouts for common-base postcomposition

This leaf gives the object, morphism, structural-isomorphism, and projection formulas for
`CategoricalPullback.postcompose`.
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

/-- Postcomposition retains the left endpoint object. -/
@[simp] theorem postcompose.obj.fst (X : F ⊡ G) :
    ((postcompose F G H).obj X).fst = X.fst := sorry

/-- Postcomposition retains the right endpoint object. -/
@[simp] theorem postcompose.obj.snd (X : F ⊡ G) :
    ((postcompose F G H).obj X).snd = X.snd := sorry

/-- Postcomposition maps the structural isomorphism by the common-base functor. -/
@[simp] theorem postcompose.obj.iso (X : F ⊡ G) :
    ((postcompose F G H).obj X).iso = H.mapIso X.iso := sorry

/-- Postcomposition retains the left component of a pullback morphism. -/
@[simp] theorem postcompose.hom.fst {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((postcompose F G H).map f).fst = f.fst := sorry

/-- Postcomposition retains the right component of a pullback morphism. -/
@[simp] theorem postcompose.hom.snd {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((postcompose F G H).map f).snd = f.snd := sorry

/-- The forward structural map after postcomposition is the image of the original map. -/
@[simp] theorem postcompose.obj.iso.hom (X : F ⊡ G) :
    ((postcompose F G H).obj X).iso.hom = H.map X.iso.hom := sorry

/-- The inverse structural map after postcomposition is the image of the original inverse. -/
@[simp] theorem postcompose.obj.iso.inv (X : F ⊡ G) :
    ((postcompose F G H).obj X).iso.inv = H.map X.iso.inv := sorry

/-- The forward component of the first projection comparison for postcomposition. -/
@[simp] theorem postcomposeFstIso.hom.app (X : F ⊡ G) :
    (postcomposeFstIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the first projection comparison for postcomposition. -/
@[simp] theorem postcomposeFstIso.inv.app (X : F ⊡ G) :
    (postcomposeFstIso F G H).inv.app X = 𝟙 _ := sorry

/-- The forward component of the second projection comparison for postcomposition. -/
@[simp] theorem postcomposeSndIso.hom.app (X : F ⊡ G) :
    (postcomposeSndIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the second projection comparison for postcomposition. -/
@[simp] theorem postcomposeSndIso.inv.app (X : F ⊡ G) :
    (postcomposeSndIso F G H).inv.app X = 𝟙 _ := sorry

end CategoryTheory.Limits.CategoricalPullback
