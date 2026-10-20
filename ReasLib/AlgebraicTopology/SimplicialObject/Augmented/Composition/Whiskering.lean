/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
@stack 0G5P

# Whiskering augmented simplicial endofunctors

An augmentation of a simplicial endofunctor can be transported along a functor on either side.
This leaf owns one-sided and two-sided whiskering together with the normalized maps on their
augmentation points.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.Functor

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

namespace SimplicialObject.Augmented

/-- Precomposition acts functorially on augmented functor-valued simplicial objects. -/
@[stacks 0G5P "precomposition of augmented functor-valued simplicial objects"]
def whiskeringLeft :
    (A ⥤ C) ⥤
      SimplicialObject.Augmented (C ⥤ B) ⥤ SimplicialObject.Augmented (A ⥤ B) :=
  Functor.whiskeringLeft A C B ⋙
    SimplicialObject.Augmented.whiskering (C ⥤ B) (A ⥤ B)

/-- Postcomposition acts functorially on augmented functor-valued simplicial objects. -/
@[stacks 0G5P "postcomposition of augmented functor-valued simplicial objects"]
def whiskeringRight :
    (C ⥤ B) ⥤
      SimplicialObject.Augmented (A ⥤ C) ⥤ SimplicialObject.Augmented (A ⥤ B) :=
  Functor.whiskeringRight A C B ⋙
    SimplicialObject.Augmented.whiskering (A ⥤ C) (A ⥤ B)

namespace whiskeringLeft

/-- The simplicial value of left whiskering is pointwise precomposition. -/
@[simp, stacks 0G5P "simplicial value of left whiskering"]
theorem obj_left_obj (F : A ⥤ C) (Q : SimplicialObject.Augmented (C ⥤ B))
    (Δ : SimplexCategoryᵒᵖ) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).obj Q).left.obj Δ =
      F ⋙ Q.left.obj Δ := sorry

/-- The point of left whiskering is precomposition of the original point. -/
@[simp, stacks 0G5P "point of left whiskering"]
theorem obj_right (F : A ⥤ C) (Q : SimplicialObject.Augmented (C ⥤ B)) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).obj Q).right =
      F ⋙ Q.right := sorry

/-- Left whiskering maps augmented morphisms degreewise by precomposition. -/
@[simp, stacks 0G5P "degreewise map of left whiskering"]
theorem obj_map_left_app (F : A ⥤ C)
    {Q R : SimplicialObject.Augmented (C ⥤ B)} (f : Q ⟶ R)
    (Δ : SimplexCategoryᵒᵖ) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).map f).left.app Δ =
      Functor.whiskerLeft F (f.left.app Δ) := sorry

/-- Left whiskering maps the point component by precomposition. -/
@[simp, stacks 0G5P "point map of left whiskering"]
theorem obj_map_right (F : A ⥤ C)
    {Q R : SimplicialObject.Augmented (C ⥤ B)} (f : Q ⟶ R) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).map f).right =
      Functor.whiskerLeft F f.right := sorry

/-- Changing the precomposition functor acts degreewise by right whiskering. -/
@[simp, stacks 0G5P "degreewise map in the precomposition variable"]
theorem map_app_left_app {F F' : A ⥤ C} (f : F ⟶ F')
    (Q : SimplicialObject.Augmented (C ⥤ B)) (Δ : SimplexCategoryᵒᵖ) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).map f).app Q).left.app Δ =
      Functor.whiskerRight f (Q.left.obj Δ) := sorry

/-- Changing the precomposition functor acts on points by right whiskering. -/
@[simp, stacks 0G5P "point map in the precomposition variable"]
theorem map_app_right {F F' : A ⥤ C} (f : F ⟶ F')
    (Q : SimplicialObject.Augmented (C ⥤ B)) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).map f).app Q).right =
      Functor.whiskerRight f Q.right := sorry

end whiskeringLeft

namespace whiskeringRight

/-- The simplicial value of right whiskering is pointwise postcomposition. -/
@[simp, stacks 0G5P "simplicial value of right whiskering"]
theorem obj_left_obj (G : C ⥤ B) (Q : SimplicialObject.Augmented (A ⥤ C))
    (Δ : SimplexCategoryᵒᵖ) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).obj Q).left.obj Δ =
      Q.left.obj Δ ⋙ G := sorry

/-- The point of right whiskering is postcomposition of the original point. -/
@[simp, stacks 0G5P "point of right whiskering"]
theorem obj_right (G : C ⥤ B) (Q : SimplicialObject.Augmented (A ⥤ C)) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).obj Q).right =
      Q.right ⋙ G := sorry

/-- Right whiskering maps augmented morphisms degreewise by postcomposition. -/
@[simp, stacks 0G5P "degreewise map of right whiskering"]
theorem obj_map_left_app (G : C ⥤ B)
    {Q R : SimplicialObject.Augmented (A ⥤ C)} (f : Q ⟶ R)
    (Δ : SimplexCategoryᵒᵖ) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).map f).left.app Δ =
      Functor.whiskerRight (f.left.app Δ) G := sorry

/-- Right whiskering maps the point component by postcomposition. -/
@[simp, stacks 0G5P "point map of right whiskering"]
theorem obj_map_right (G : C ⥤ B)
    {Q R : SimplicialObject.Augmented (A ⥤ C)} (f : Q ⟶ R) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).map f).right =
      Functor.whiskerRight f.right G := sorry

/-- Changing the postcomposition functor acts degreewise by left whiskering. -/
@[simp, stacks 0G5P "degreewise map in the postcomposition variable"]
theorem map_app_left_app {G G' : C ⥤ B} (g : G ⟶ G')
    (Q : SimplicialObject.Augmented (A ⥤ C)) (Δ : SimplexCategoryᵒᵖ) :
    (((whiskeringRight (A := A) (C := C) (B := B)).map g).app Q).left.app Δ =
      Functor.whiskerLeft (Q.left.obj Δ) g := sorry

/-- Changing the postcomposition functor acts on points by left whiskering. -/
@[simp, stacks 0G5P "point map in the postcomposition variable"]
theorem map_app_right {G G' : C ⥤ B} (g : G ⟶ G')
    (Q : SimplicialObject.Augmented (A ⥤ C)) :
    (((whiskeringRight (A := A) (C := C) (B := B)).map g).app Q).right =
      Functor.whiskerLeft Q.right g := sorry

end whiskeringRight

/-- The augmentation obtained from `X ⟶ 𝟭 C` by precomposing with `F`. -/
@[stacks 0G5P "precomposition of an augmented simplicial endofunctor"]
abbrev precompose (F : A ⥤ C)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    SimplicialObject.Augmented (A ⥤ C) :=
  ((whiskeringLeft (A := A) (C := C) (B := C)).obj F).obj
    { left := X
      right := 𝟭 C
      hom := ε }

/-- The augmentation obtained from `X ⟶ 𝟭 C` by postcomposing with `G`. -/
@[stacks 0G5P "postcomposition of an augmented simplicial endofunctor"]
abbrev postcompose (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    SimplicialObject.Augmented (C ⥤ B) :=
  ((whiskeringRight (A := C) (C := C) (B := B)).obj G).obj
    { left := X
      right := 𝟭 C
      hom := ε }

namespace precompose

/-- Extract the normalized point map from a morphism between precomposed augmentations. -/
@[stacks 0G5R "point map of a precomposition-compatible simplicial morphism"]
def point {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} (f : precompose F ε ⟶ precompose F' ε) : F ⟶ F' :=
  (Functor.rightUnitor F).inv ≫ f.right ≫ (Functor.rightUnitor F').hom

/-- Normalized precomposition points preserve identity morphisms. -/
@[simp, stacks 0G5R "normalized precomposition preserves identities"]
theorem point_id {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) (F : A ⥤ C) :
    point (𝟙 (precompose F ε)) = 𝟙 F := sorry

/-- Normalized precomposition points preserve composition. -/
@[simp, stacks 0G5R "normalized precomposition preserves composition"]
theorem point_comp {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F₀ F₁ F₂ : A ⥤ C}
    (f : precompose F₀ ε ⟶ precompose F₁ ε)
    (g : precompose F₁ ε ⟶ precompose F₂ ε) :
    point (f ≫ g) = point f ≫ point g := sorry

/-- Change the functor on the left of an augmented simplicial endofunctor. -/
@[stacks 0G5R "map induced by changing a precomposition functor"]
def map {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {F F' : A ⥤ C} (f : F ⟶ F') :
    precompose F ε ⟶ precompose F' ε :=
  ((whiskeringLeft (A := A) (C := C) (B := C)).map f).app
    ({ left := X
       right := 𝟭 C
       hom := ε } : SimplicialObject.Augmented (C ⥤ C))

/-- The simplicial components of `precompose.map` are right whiskering maps. -/
@[simp, stacks 0G5R "degreewise map induced by changing a precomposition functor"]
theorem map_left_app {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {F F' : A ⥤ C} (f : F ⟶ F') (Δ : SimplexCategoryᵒᵖ) :
    (map ε f).left.app Δ = Functor.whiskerRight f (X.obj Δ) := sorry

/-- The point component of `precompose.map` is right whiskering by the identity functor. -/
@[simp, stacks 0G5R "point map induced by changing a precomposition functor"]
theorem map_right {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {F F' : A ⥤ C} (f : F ⟶ F') :
    (map ε f).right = Functor.whiskerRight f (𝟭 C) := sorry

/-- Normalizing the point of `precompose.map` recovers the original map. -/
@[simp, stacks 0G5R "normalized point of a changed precomposition functor"]
theorem point_map {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {F F' : A ⥤ C} (f : F ⟶ F') :
    point (map ε f) = f := sorry

end precompose

namespace postcompose

/-- Extract the normalized point map from a morphism between postcomposed augmentations. -/
@[stacks 0G5R "point map of a postcomposition-compatible simplicial morphism"]
def point {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {G G' : C ⥤ B} (g : postcompose G ε ⟶ postcompose G' ε) : G ⟶ G' :=
  (Functor.leftUnitor G).inv ≫ g.right ≫ (Functor.leftUnitor G').hom

/-- Normalized postcomposition points preserve identity morphisms. -/
@[simp, stacks 0G5R "normalized postcomposition preserves identities"]
theorem point_id {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) (G : C ⥤ B) :
    point (𝟙 (postcompose G ε)) = 𝟙 G := sorry

/-- Normalized postcomposition points preserve composition. -/
@[simp, stacks 0G5R "normalized postcomposition preserves composition"]
theorem point_comp {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {G₀ G₁ G₂ : C ⥤ B}
    (f : postcompose G₀ ε ⟶ postcompose G₁ ε)
    (g : postcompose G₁ ε ⟶ postcompose G₂ ε) :
    point (f ≫ g) = point f ≫ point g := sorry

/-- Change the functor on the right of an augmented simplicial endofunctor. -/
@[stacks 0G5R "map induced by changing a postcomposition functor"]
def map {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {G G' : C ⥤ B} (g : G ⟶ G') :
    postcompose G ε ⟶ postcompose G' ε :=
  ((whiskeringRight (A := C) (C := C) (B := B)).map g).app
    ({ left := X
       right := 𝟭 C
       hom := ε } : SimplicialObject.Augmented (C ⥤ C))

/-- The simplicial components of `postcompose.map` are left whiskering maps. -/
@[simp, stacks 0G5R "degreewise map induced by changing a postcomposition functor"]
theorem map_left_app {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {G G' : C ⥤ B} (g : G ⟶ G') (Δ : SimplexCategoryᵒᵖ) :
    (map ε g).left.app Δ = Functor.whiskerLeft (X.obj Δ) g := sorry

/-- The point component of `postcompose.map` is left whiskering by the identity functor. -/
@[simp, stacks 0G5R "point map induced by changing a postcomposition functor"]
theorem map_right {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {G G' : C ⥤ B} (g : G ⟶ G') :
    (map ε g).right = Functor.whiskerLeft (𝟭 C) g := sorry

/-- Normalizing the point of `postcompose.map` recovers the original map. -/
@[simp, stacks 0G5R "normalized point of a changed postcomposition functor"]
theorem point_map {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    {G G' : C ⥤ B} (g : G ⟶ G') :
    point (map ε g) = g := sorry

end postcompose

/-- Whisker an augmented simplicial endofunctor on both sides. -/
@[stacks 0G5R "two-sided whiskering of an augmented simplicial endofunctor"]
def whisker (F : A ⥤ C) (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    SimplicialObject.Augmented (A ⥤ B) :=
  ((whiskeringLeft (A := A) (C := C) (B := B)).obj F).obj (postcompose G ε)

namespace whisker

/-- In each simplicial degree, two-sided whiskering is composition on both sides. -/
@[simp, stacks 0G5R "degreewise two-sided whiskering"]
theorem left_obj (F : A ⥤ C) (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (Δ : SimplexCategoryᵒᵖ) :
    (whisker F G ε).left.obj Δ = F ⋙ (X.obj Δ ⋙ G) := sorry

/-- The point of two-sided whiskering retains the canonical functor-composition bracketing. -/
@[simp, stacks 0G5R "point of two-sided whiskering"]
theorem right (F : A ⥤ C) (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    (whisker F G ε).right = F ⋙ ((𝟭 C) ⋙ G) := sorry

/-- In each simplicial degree, the augmentation of two-sided whiskering is obtained by
pre- and postwhiskering the original augmentation. -/
@[simp, stacks 0G5P "augmentation component of two-sided whiskering"]
theorem hom_app (F : A ⥤ C) (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (Δ : SimplexCategoryᵒᵖ) :
    (whisker F G ε).hom.app Δ =
      Functor.whiskerLeft F (Functor.whiskerRight (ε.app Δ) G) := sorry

/-- The canonical identification of the augmented point with `F ⋙ G`. -/
@[stacks 0G5R "normalized point of two-sided whiskering"]
def pointIso (F : A ⥤ C) (G : C ⥤ B)
    {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) :
    (whisker F G ε).right ≅ F ⋙ G :=
  Functor.isoWhiskerLeft F (Functor.leftUnitor G)

/-- Normalize the point component of a morphism between two-sided whiskerings. -/
@[stacks 0G5R "point map of a two-sided-whiskering morphism"]
def point {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (f : whisker F G ε ⟶ whisker F' G' ε) : F ⋙ G ⟶ F' ⋙ G' :=
  (pointIso F G ε).inv ≫ f.right ≫ (pointIso F' G' ε).hom

/-- Normalized two-sided points preserve identity morphisms. -/
@[simp, stacks 0G5R "normalized two-sided whiskering preserves identities"]
theorem point_id {X : SimplicialObject (C ⥤ C)}
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (F : A ⥤ C) (G : C ⥤ B) :
    point (𝟙 (whisker F G ε)) = 𝟙 (F ⋙ G) := sorry

/-- Normalized two-sided points preserve composition. -/
@[simp, stacks 0G5R "normalized two-sided whiskering preserves composition"]
theorem point_comp {X : SimplicialObject (C ⥤ C)}
    {ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)}
    {F₀ F₁ F₂ : A ⥤ C} {G₀ G₁ G₂ : C ⥤ B}
    (f : whisker F₀ G₀ ε ⟶ whisker F₁ G₁ ε)
    (g : whisker F₁ G₁ ε ⟶ whisker F₂ G₂ ε) :
    point (f ≫ g) = point f ≫ point g := sorry

end whisker

end SimplicialObject.Augmented

end CategoryTheory
