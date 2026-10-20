module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Natural Transformations as Arrow Functors

This module packages the components of a natural transformation as a functor to the arrow
category.  The two orientations support functorial injective embeddings and functorial
projective surjections without making either construction depend on the other.
-/

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

/-- Turn a natural transformation `η : F ⟶ G` into its functorial family of component
arrows. -/
@[stacks 019I "natural transformation arrow functor",
  stacks 01D9 "free-presentation arrow functor"]
noncomputable def NatTrans.arrowFunctor
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ Arrow D where
  obj X := Arrow.mk (η.app X)
  map f := Arrow.homMk' (F.map f) (G.map f) (η.naturality f)
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The arrow over `X` classified by `η.arrowFunctor` is the component `η.app X`. -/
@[simp, stacks 019I "natural transformation arrow functor object formula"]
theorem NatTrans.arrowFunctor.obj.hom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (η.arrowFunctor.obj X).hom = η.app X := sorry

/-- The left side of the square classified by `η.arrowFunctor.map f` is `F.map f`. -/
@[simp, stacks 019I "natural transformation arrow functor left map formula"]
theorem NatTrans.arrowFunctor.map.left
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (η.arrowFunctor.map f).left = F.map f := sorry

/-- The right side of the square classified by `η.arrowFunctor.map f` is `G.map f`. -/
@[simp, stacks 019I "natural transformation arrow functor right map formula"]
theorem NatTrans.arrowFunctor.map.right
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (η.arrowFunctor.map f).right = G.map f := sorry

/-- The source functor of `NatTrans.arrowFunctor η` is `F`. -/
@[simp, stacks 019I "source of the natural transformation arrow functor"]
theorem NatTrans.arrowFunctor.comp.left
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (η : F ⟶ G) :
    η.arrowFunctor ⋙ Arrow.leftFunc = F := sorry

/-- The target functor of `NatTrans.arrowFunctor η` is `G`. -/
@[simp, stacks 019I "target of the natural transformation arrow functor"]
theorem NatTrans.arrowFunctor.comp.right
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (η : F ⟶ G) :
    η.arrowFunctor ⋙ Arrow.rightFunc = G := sorry

namespace NatTrans

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D} [HasImages D] [HasImageMaps D]

/-- The functor obtained by taking the categorical image of every component of a natural
transformation. -/
@[stacks 019I "componentwise image functor of a natural transformation"]
noncomputable def imageFunctor (η : F ⟶ G) : C ⥤ D :=
  η.arrowFunctor ⋙ Limits.im

/-- The componentwise image functor evaluates to the image of the corresponding component. -/
@[simp, stacks 019I "componentwise image functor object formula"]
theorem imageFunctor.obj (η : F ⟶ G) (X : C) :
    η.imageFunctor.obj X = image (η.app X) := sorry

/-- The componentwise image functor maps a morphism by the canonical map between images of the
naturality square. -/
@[simp, stacks 019I "componentwise image functor map formula"]
theorem imageFunctor.map (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    η.imageFunctor.map f =
      image.map (Arrow.homMk' (F.map f) (G.map f) (η.naturality f)) := sorry

/-- Factoring the components of a natural transformation through their images is natural. -/
@[stacks 019I "naturality of componentwise image factorization"]
theorem factorThruImage.naturality (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ Limits.factorThruImage (η.app Y) =
      Limits.factorThruImage (η.app X) ≫ η.imageFunctor.map f := sorry

/-- The natural transformation from the source to the componentwise image. -/
@[stacks 019I "componentwise image factorization"]
noncomputable def factorThruImage (η : F ⟶ G) : F ⟶ η.imageFunctor where
  app X := Limits.factorThruImage (η.app X)
  naturality _ _ f := factorThruImage.naturality η f

/-- The component of the natural factorization through the image is the canonical factor. -/
@[simp, stacks 019I "componentwise image factorization component"]
theorem factorThruImage.app (η : F ⟶ G) (X : C) :
    (NatTrans.factorThruImage η).app X = Limits.factorThruImage (η.app X) := sorry

/-- The componentwise image inclusions are natural. -/
@[stacks 019I "naturality of componentwise image inclusion"]
theorem image.ι.naturality (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    η.imageFunctor.map f ≫ Limits.image.ι (η.app Y) =
      Limits.image.ι (η.app X) ≫ G.map f := sorry

/-- The natural inclusion from the componentwise image to the target. -/
@[stacks 019I "componentwise image inclusion"]
noncomputable def image.ι (η : F ⟶ G) : η.imageFunctor ⟶ G where
  app X := Limits.image.ι (η.app X)
  naturality _ _ f := image.ι.naturality η f

/-- The component of the natural image inclusion is the canonical image monomorphism. -/
@[simp, stacks 019I "componentwise image inclusion component"]
theorem image.ι.app (η : F ⟶ G) (X : C) :
    (NatTrans.image.ι η).app X = Limits.image.ι (η.app X) := sorry

/-- The natural factorization through the componentwise image recovers the original natural
transformation. -/
@[reassoc, stacks 019I "componentwise image factorization formula"]
theorem factorThruImage_comp_ι (η : F ⟶ G) :
    NatTrans.factorThruImage η ≫ NatTrans.image.ι η = η := sorry

end NatTrans

end CategoryTheory

