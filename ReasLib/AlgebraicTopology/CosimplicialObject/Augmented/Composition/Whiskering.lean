module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.Composition.Pointwise

/-!
# Whiskering augmented cosimplicial objects

This leaf owns two-sided composition of augmented cosimplicial functor objects, including the
precomposition and postcomposition interfaces for augmented endofunctors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.CosimplicialObject
open CategoryTheory.Functor

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

namespace CosimplicialObject.Augmented

/-- Precomposition acts functorially on augmented functor-valued cosimplicial objects. -/
@[stacks 0G5P "precomposition of augmented functor-valued cosimplicial objects"]
def whiskeringLeft :
    (A ⥤ C) ⥤
      CosimplicialObject.Augmented (C ⥤ B) ⥤ CosimplicialObject.Augmented (A ⥤ B) :=
  Functor.whiskeringLeft A C B ⋙
    CosimplicialObject.Augmented.whiskering (C ⥤ B) (A ⥤ B)

/-- Postcomposition acts functorially on augmented functor-valued cosimplicial objects. -/
@[stacks 0G5P "postcomposition of augmented functor-valued cosimplicial objects"]
def whiskeringRight :
    (C ⥤ B) ⥤
      CosimplicialObject.Augmented (A ⥤ C) ⥤ CosimplicialObject.Augmented (A ⥤ B) :=
  Functor.whiskeringRight A C B ⋙
    CosimplicialObject.Augmented.whiskering (A ⥤ C) (A ⥤ B)

namespace whiskeringLeft

/-- The point of left whiskering is precomposition of the original point. -/
@[simp, stacks 0G5P "point of left whiskering for augmented cosimplicial objects"]
theorem obj_left (F : A ⥤ C) (Q : CosimplicialObject.Augmented (C ⥤ B)) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).obj Q).left =
      F ⋙ Q.left := sorry

/-- The cosimplicial value of left whiskering is pointwise precomposition. -/
@[simp, stacks 0G5P "cosimplicial value of left whiskering"]
theorem obj_right_obj (F : A ⥤ C) (Q : CosimplicialObject.Augmented (C ⥤ B))
    (Δ : SimplexCategory) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).obj Q).right.obj Δ =
      F ⋙ Q.right.obj Δ := sorry

/-- The coaugmentation of left whiskering is pointwise precomposition. -/
@[simp, stacks 0G5P "coaugmentation component of left whiskering"]
theorem obj_hom_app (F : A ⥤ C) (Q : CosimplicialObject.Augmented (C ⥤ B))
    (Δ : SimplexCategory) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).obj Q).hom.app Δ =
      Functor.whiskerLeft F (Q.hom.app Δ) := sorry

/-- Left whiskering maps the point component by precomposition. -/
@[simp, stacks 0G5P "point map of left whiskering for augmented cosimplicial objects"]
theorem obj_map_left (F : A ⥤ C)
    {Q R : CosimplicialObject.Augmented (C ⥤ B)} (f : Q ⟶ R) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).map f).left =
      Functor.whiskerLeft F f.left := sorry

/-- Left whiskering maps augmented cosimplicial morphisms degreewise by precomposition. -/
@[simp, stacks 0G5P "degreewise map of left whiskering for augmented cosimplicial objects"]
theorem obj_map_right_app (F : A ⥤ C)
    {Q R : CosimplicialObject.Augmented (C ⥤ B)} (f : Q ⟶ R)
    (Δ : SimplexCategory) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).obj F).map f).right.app Δ =
      Functor.whiskerLeft F (f.right.app Δ) := sorry

/-- Changing the precomposition functor acts on points by right whiskering. -/
@[simp, stacks 0G5P "point map in the cosimplicial precomposition variable"]
theorem map_app_left {F F' : A ⥤ C} (f : F ⟶ F')
    (Q : CosimplicialObject.Augmented (C ⥤ B)) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).map f).app Q).left =
      Functor.whiskerRight f Q.left := sorry

/-- Changing the precomposition functor acts degreewise by right whiskering. -/
@[simp, stacks 0G5P "degreewise map in the cosimplicial precomposition variable"]
theorem map_app_right_app {F F' : A ⥤ C} (f : F ⟶ F')
    (Q : CosimplicialObject.Augmented (C ⥤ B)) (Δ : SimplexCategory) :
    (((whiskeringLeft (A := A) (C := C) (B := B)).map f).app Q).right.app Δ =
      Functor.whiskerRight f (Q.right.obj Δ) := sorry

end whiskeringLeft

namespace whiskeringRight

/-- The point of right whiskering is postcomposition of the original point. -/
@[simp, stacks 0G5P "point of right whiskering for augmented cosimplicial objects"]
theorem obj_left (G : C ⥤ B) (Q : CosimplicialObject.Augmented (A ⥤ C)) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).obj Q).left =
      Q.left ⋙ G := sorry

/-- The cosimplicial value of right whiskering is pointwise postcomposition. -/
@[simp, stacks 0G5P "cosimplicial value of right whiskering"]
theorem obj_right_obj (G : C ⥤ B) (Q : CosimplicialObject.Augmented (A ⥤ C))
    (Δ : SimplexCategory) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).obj Q).right.obj Δ =
      Q.right.obj Δ ⋙ G := sorry

/-- The coaugmentation of right whiskering is pointwise postcomposition. -/
@[simp, stacks 0G5P "coaugmentation component of right whiskering"]
theorem obj_hom_app (G : C ⥤ B) (Q : CosimplicialObject.Augmented (A ⥤ C))
    (Δ : SimplexCategory) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).obj Q).hom.app Δ =
      Functor.whiskerRight (Q.hom.app Δ) G := sorry

/-- Right whiskering maps the point component by postcomposition. -/
@[simp, stacks 0G5P "point map of right whiskering for augmented cosimplicial objects"]
theorem obj_map_left (G : C ⥤ B)
    {Q R : CosimplicialObject.Augmented (A ⥤ C)} (f : Q ⟶ R) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).map f).left =
      Functor.whiskerRight f.left G := sorry

/-- Right whiskering maps augmented cosimplicial morphisms degreewise by postcomposition. -/
@[simp, stacks 0G5P "degreewise map of right whiskering for augmented cosimplicial objects"]
theorem obj_map_right_app (G : C ⥤ B)
    {Q R : CosimplicialObject.Augmented (A ⥤ C)} (f : Q ⟶ R)
    (Δ : SimplexCategory) :
    (((whiskeringRight (A := A) (C := C) (B := B)).obj G).map f).right.app Δ =
      Functor.whiskerRight (f.right.app Δ) G := sorry

/-- Changing the postcomposition functor acts on points by left whiskering. -/
@[simp, stacks 0G5P "point map in the cosimplicial postcomposition variable"]
theorem map_app_left {G G' : C ⥤ B} (g : G ⟶ G')
    (Q : CosimplicialObject.Augmented (A ⥤ C)) :
    (((whiskeringRight (A := A) (C := C) (B := B)).map g).app Q).left =
      Functor.whiskerLeft Q.left g := sorry

/-- Changing the postcomposition functor acts degreewise by left whiskering. -/
@[simp, stacks 0G5P "degreewise map in the cosimplicial postcomposition variable"]
theorem map_app_right_app {G G' : C ⥤ B} (g : G ⟶ G')
    (Q : CosimplicialObject.Augmented (A ⥤ C)) (Δ : SimplexCategory) :
    (((whiskeringRight (A := A) (C := C) (B := B)).map g).app Q).right.app Δ =
      Functor.whiskerLeft (Q.right.obj Δ) g := sorry

end whiskeringRight

/-- The coaugmentation obtained from `𝟭 C ⟶ X` by precomposing with `F`. -/
@[stacks 0G5P "precomposition of an augmented cosimplicial endofunctor"]
abbrev precompose (F : A ⥤ C)
    {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X) :
    CosimplicialObject.Augmented (A ⥤ C) :=
  ((whiskeringLeft (A := A) (C := C) (B := C)).obj F).obj
    { left := 𝟭 C
      right := X
      hom := η }

/-- The coaugmentation obtained from `𝟭 C ⟶ X` by postcomposing with `G`. -/
@[stacks 0G5P "postcomposition of an augmented cosimplicial endofunctor"]
abbrev postcompose (G : C ⥤ B)
    {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X) :
    CosimplicialObject.Augmented (C ⥤ B) :=
  ((whiskeringRight (A := C) (C := C) (B := B)).obj G).obj
    { left := 𝟭 C
      right := X
      hom := η }

namespace precompose

/-- The point of a precomposed coaugmentation is the precomposition functor followed by the
identity endofunctor. -/
@[simp, stacks 0G5P "point of a precomposed augmented cosimplicial endofunctor"]
theorem left (F : A ⥤ C) {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X) :
    (precompose F η).left = F ⋙ 𝟭 C := sorry

/-- Degreewise, precomposition acts on the source of the endofunctor. -/
@[simp, stacks 0G5P "degree of a precomposed augmented cosimplicial endofunctor"]
theorem right_obj (F : A ⥤ C) {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    (Δ : SimplexCategory) :
    (precompose F η).right.obj Δ = F ⋙ X.obj Δ := sorry

/-- The coaugmentation of a precomposed augmented endofunctor is left whiskering of the
original coaugmentation. -/
@[simp, stacks 0G5P "coaugmentation component after precomposition"]
theorem hom_app (F : A ⥤ C) {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    (Δ : SimplexCategory) :
    (precompose F η).hom.app Δ = Functor.whiskerLeft F (η.app Δ) := sorry

/-- Extract the normalized point map from a morphism between precomposed coaugmentations. -/
@[stacks 0G5R "point map of a precomposition-compatible cosimplicial morphism"]
def point {X : CosimplicialObject (C ⥤ C)}
    {η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X}
    {F F' : A ⥤ C} (f : precompose F η ⟶ precompose F' η) : F ⟶ F' :=
  (Functor.rightUnitor F).inv ≫ f.left ≫ (Functor.rightUnitor F').hom

/-- Normalized precomposition points preserve identity morphisms. -/
@[simp, stacks 0G5R "normalized cosimplicial precomposition preserves identities"]
theorem point_id {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X) (F : A ⥤ C) :
    point (𝟙 (precompose F η)) = 𝟙 F := sorry

/-- Normalized precomposition points preserve composition. -/
@[simp, stacks 0G5R "normalized cosimplicial precomposition preserves composition"]
theorem point_comp {X : CosimplicialObject (C ⥤ C)}
    {η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X}
    {F₀ F₁ F₂ : A ⥤ C}
    (f : precompose F₀ η ⟶ precompose F₁ η)
    (g : precompose F₁ η ⟶ precompose F₂ η) :
    point (f ≫ g) = point f ≫ point g := sorry

/-- Change the functor on the left of an augmented cosimplicial endofunctor. -/
@[stacks 0G5R "map induced by changing a cosimplicial precomposition functor"]
def map {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {F F' : A ⥤ C} (f : F ⟶ F') : precompose F η ⟶ precompose F' η :=
  ((whiskeringLeft (A := A) (C := C) (B := C)).map f).app
    ({ left := 𝟭 C, right := X, hom := η } : CosimplicialObject.Augmented (C ⥤ C))

/-- The point component of `precompose.map` is right whiskering with the identity functor. -/
@[simp, stacks 0G5R "point component of a cosimplicial precomposition map"]
theorem map_left {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {F F' : A ⥤ C} (f : F ⟶ F') :
    (map η f).left = Functor.whiskerRight f (𝟭 C) := sorry

/-- The degreewise component of `precompose.map` is right whiskering with the original
endofunctor. -/
@[simp, stacks 0G5R "degreewise component of a cosimplicial precomposition map"]
theorem map_right_app {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {F F' : A ⥤ C} (f : F ⟶ F') (Δ : SimplexCategory) :
    (map η f).right.app Δ = Functor.whiskerRight f (X.obj Δ) := sorry

/-- Extracting the normalized point of a canonical precomposition map recovers the given
natural transformation. -/
@[simp, stacks 0G5R "normalized point of a cosimplicial precomposition map"]
theorem point_map {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {F F' : A ⥤ C} (f : F ⟶ F') : point (map η f) = f := sorry

end precompose

namespace postcompose

/-- The point of a postcomposed coaugmentation is the identity endofunctor followed by the
postcomposition functor. -/
@[simp, stacks 0G5P "point of a postcomposed augmented cosimplicial endofunctor"]
theorem left (G : C ⥤ B) {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X) :
    (postcompose G η).left = 𝟭 C ⋙ G := sorry

/-- Degreewise, postcomposition acts on the target of the endofunctor. -/
@[simp, stacks 0G5P "degree of a postcomposed augmented cosimplicial endofunctor"]
theorem right_obj (G : C ⥤ B) {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    (Δ : SimplexCategory) :
    (postcompose G η).right.obj Δ = X.obj Δ ⋙ G := sorry

/-- The coaugmentation of a postcomposed augmented endofunctor is right whiskering of the
original coaugmentation. -/
@[simp, stacks 0G5P "coaugmentation component after postcomposition"]
theorem hom_app (G : C ⥤ B) {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    (Δ : SimplexCategory) :
    (postcompose G η).hom.app Δ = Functor.whiskerRight (η.app Δ) G := sorry

/-- Extract the normalized point map from a morphism between postcomposed coaugmentations. -/
@[stacks 0G5R "point map of a postcomposition-compatible cosimplicial morphism"]
def point {X : CosimplicialObject (C ⥤ C)}
    {η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X}
    {G G' : C ⥤ B} (g : postcompose G η ⟶ postcompose G' η) : G ⟶ G' :=
  (Functor.leftUnitor G).inv ≫ g.left ≫ (Functor.leftUnitor G').hom

/-- Normalized postcomposition points preserve identity morphisms. -/
@[simp, stacks 0G5R "normalized cosimplicial postcomposition preserves identities"]
theorem point_id {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X) (G : C ⥤ B) :
    point (𝟙 (postcompose G η)) = 𝟙 G := sorry

/-- Normalized postcomposition points preserve composition. -/
@[simp, stacks 0G5R "normalized cosimplicial postcomposition preserves composition"]
theorem point_comp {X : CosimplicialObject (C ⥤ C)}
    {η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X}
    {G₀ G₁ G₂ : C ⥤ B}
    (f : postcompose G₀ η ⟶ postcompose G₁ η)
    (g : postcompose G₁ η ⟶ postcompose G₂ η) :
    point (f ≫ g) = point f ≫ point g := sorry

/-- Change the functor on the right of an augmented cosimplicial endofunctor. -/
@[stacks 0G5R "map induced by changing a cosimplicial postcomposition functor"]
def map {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {G G' : C ⥤ B} (g : G ⟶ G') : postcompose G η ⟶ postcompose G' η :=
  ((whiskeringRight (A := C) (C := C) (B := B)).map g).app
    ({ left := 𝟭 C, right := X, hom := η } : CosimplicialObject.Augmented (C ⥤ C))

/-- The point component of `postcompose.map` is left whiskering with the identity functor. -/
@[simp, stacks 0G5R "point component of a cosimplicial postcomposition map"]
theorem map_left {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {G G' : C ⥤ B} (g : G ⟶ G') :
    (map η g).left = Functor.whiskerLeft (𝟭 C) g := sorry

/-- The degreewise component of `postcompose.map` is left whiskering with the original
endofunctor. -/
@[simp, stacks 0G5R "degreewise component of a cosimplicial postcomposition map"]
theorem map_right_app {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {G G' : C ⥤ B} (g : G ⟶ G') (Δ : SimplexCategory) :
    (map η g).right.app Δ = Functor.whiskerLeft (X.obj Δ) g := sorry

/-- Extracting the normalized point of a canonical postcomposition map recovers the given
natural transformation. -/
@[simp, stacks 0G5R "normalized point of a cosimplicial postcomposition map"]
theorem point_map {X : CosimplicialObject (C ⥤ C)}
    (η : (CosimplicialObject.const (C ⥤ C)).obj (𝟭 C) ⟶ X)
    {G G' : C ⥤ B} (g : G ⟶ G') : point (map η g) = g := sorry

end postcompose

end CosimplicialObject.Augmented

end CategoryTheory
