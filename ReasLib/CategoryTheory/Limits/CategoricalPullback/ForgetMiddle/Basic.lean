/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map

/-!
# Middle contraction for iterated categorical pullbacks

The cospan transformation and explicit forward and inverse functors underlying middle
contraction. Computation rules and equivalence data live in separate leaf modules.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

open Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

variable (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

local notation "LeftAssoc" => (π₂ F G) ⊡ H
local notation "RightAssoc" => F ⊡ (H ⋙ G)

namespace Limits.CategoricalPullback.ForgetMiddle

/- This comparison is not merely `CategoricalPullback.associativity`: after changing brackets it
contracts the identity pullback over `C`. Its reusable owner is the cospan transformation below,
followed by the generic `CategoricalPullback.map` construction. -/

/-- The cospan transformation that contracts the middle category in
`(F ⊡ G) ×_C D`. -/
def transform : CatCospanTransform (π₂ F G) H F (H ⋙ G) :=
  { left := π₁ F G
    base := G
    right := 𝟭 D
    squareLeft := ⟨(catCommSq F G).iso.symm⟩
    squareRight := ⟨(leftUnitor (H ⋙ G)).symm⟩ }

/-- The canonical forward functor that forgets the middle object and composes the two structural
isomorphisms. -/
def functor : LeftAssoc ⥤ RightAssoc :=
  map (transform F G H)

namespace functor

/-- Projecting middle contraction to the leftmost category recovers the two successive first
projections. -/
def fstIso :
    functor F G H ⋙ π₁ F (H ⋙ G) ≅
      π₁ (π₂ F G) H ⋙ π₁ F G :=
  mapFstIso (transform F G H)

/-- Projecting middle contraction to the rightmost category recovers the source's second
projection. -/
def sndIso :
    functor F G H ⋙ π₂ F (H ⋙ G) ≅
      π₂ (π₂ F G) H :=
  mapSndIso (transform F G H) ≪≫ Functor.rightUnitor _

end functor

section Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace inverse.Implementation

/-- Insert the canonical middle object into a contracted pullback object:
`(a, d, θ) ↦ ((a, H.obj d, θ), d, Iso.refl _)`. -/
private def insertMiddleObj (X : RightAssoc) : LeftAssoc where
  fst :=
    { fst := X.fst
      snd := H.obj X.snd
      iso := X.iso }
  snd := X.snd
  iso := Iso.refl _

/-- Compatibility of the two visible components of the inserted inner pullback morphism. -/
private theorem insertMiddleFstMap_w {X Y : RightAssoc} (f : X ⟶ Y) :
    F.map f.fst ≫ (insertMiddleObj F G H Y).fst.iso.hom =
      (insertMiddleObj F G H X).fst.iso.hom ≫ G.map (H.map f.snd) := sorry

/-- The inner pullback component of a morphism after inserting the middle object. -/
private def insertMiddleFstMap {X Y : RightAssoc} (f : X ⟶ Y) :
    (insertMiddleObj F G H X).fst ⟶ (insertMiddleObj F G H Y).fst where
  fst := f.fst
  snd := H.map f.snd
  w := insertMiddleFstMap_w F G H f

/-- Compatibility of the inserted inner morphism with the outer identity structural
isomorphisms. -/
private theorem insertMiddleMap_w {X Y : RightAssoc} (f : X ⟶ Y) :
    (π₂ F G).map (insertMiddleFstMap F G H f) ≫
        (insertMiddleObj F G H Y).iso.hom =
      (insertMiddleObj F G H X).iso.hom ≫ H.map f.snd := sorry

/-- Insert the middle component of a morphism by applying `H` to its right component. -/
private def insertMiddleMap {X Y : RightAssoc} (f : X ⟶ Y) :
    insertMiddleObj F G H X ⟶ insertMiddleObj F G H Y where
  fst := insertMiddleFstMap F G H f
  snd := f.snd
  w := insertMiddleMap_w F G H f

/-- Inserting the middle object preserves identity morphisms. -/
private theorem insertMiddleMapId (X : RightAssoc) :
    insertMiddleMap F G H (𝟙 X) = 𝟙 (insertMiddleObj F G H X) := sorry

/-- Inserting the middle object preserves composition of morphisms. -/
private theorem insertMiddleMapComp {X Y Z : RightAssoc} (f : X ⟶ Y) (g : Y ⟶ Z) :
    insertMiddleMap F G H (f ≫ g) =
      insertMiddleMap F G H f ≫ insertMiddleMap F G H g := sorry

end inverse.Implementation

/-- The explicit inverse functor to `functor`, obtained by inserting `H.obj d` as the middle
object. -/
def inverse : RightAssoc ⥤ LeftAssoc where
  obj := inverse.Implementation.insertMiddleObj F G H
  map := inverse.Implementation.insertMiddleMap F G H
  map_id := inverse.Implementation.insertMiddleMapId F G H
  map_comp := inverse.Implementation.insertMiddleMapComp F G H

end Implementation

end Limits.CategoricalPullback.ForgetMiddle

end CategoryTheory
