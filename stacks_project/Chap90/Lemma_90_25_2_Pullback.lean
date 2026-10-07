module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap90.Definition_90_21_1_Groupoid
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel pair of a morphism of categories cofibered in groupoids

From a morphism `f : ofTypeValued U ⟶ F`, this module constructs the Type-valued functor
`R = U ×_{f, F, f} U` together with the first and second projections and the first-and-last
composition map of the associated groupoid in functors.
-/

@[expose] public section

open CategoryTheory Limits Functor TypeCat
open scoped BasedFunctor

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]
variable {U : C ⥤ Type (max v w)}
variable {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C}

/-- The total functor underlying a morphism `ofTypeValued U ⟶ F`. -/
abbrev totalMap (f : Functor.ofTypeValued U ⟶ F) :
    (Functor.ofTypeValued U).total ⥤ F.total :=
  CofiberedCategoryOver.Groupoids.toFunctor f

/-- The fibre object of `CategoryOfElements.π U` associated to an element of `U.obj T`. -/
def objectFiber (T : C) (x : U.obj T) : (CategoryOfElements.π U).Fiber T :=
  ⟨⟨T, x⟩, rfl⟩

/-- The `U`-value carried by a fibre of the category of elements. -/
def fiberToObj {T : C} (x : (CategoryOfElements.π U).Fiber T) : U.obj T :=
  match x with
  | ⟨⟨_, val⟩, h⟩ => h ▸ val

/-- The image of an object of `U` in the total category of `F`. -/
def imageObj (f : Functor.ofTypeValued U ⟶ F) (T : C) (x : U.obj T) : F.total :=
  (totalMap f).obj ⟨T, x⟩

/-- The unique morphism of elements over a base arrow `φ`. -/
def elementsArrow {T T' : C} (φ : T ⟶ T') (x : U.obj T) :
    { g : T ⟶ T' // U.map g x = U.map φ x } :=
  ⟨φ, rfl⟩

/-- The image in `F` of the unique elements-arrow over `φ`. -/
def imageLift (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (x : U.obj T) :
    imageObj f T x ⟶ imageObj f T' (U.map φ x) :=
  (totalMap f).map (elementsArrow φ x)

/-- An arrow of the kernel pair: a pair of objects of `U` together with an isomorphism of
their images in the fibre of `F`. -/
structure Arrow (f : Functor.ofTypeValued U ⟶ F) (T : C) where
  /-- The first factor, which is the target of the arrow. -/
  left : U.obj T
  /-- The second factor, which is the source of the arrow. -/
  right : U.obj T
  /-- The forward isomorphism of images in `F`. -/
  hom : imageObj f T left ⟶ imageObj f T right
  /-- The inverse isomorphism of images in `F`. -/
  inv : imageObj f T right ⟶ imageObj f T left
  /-- `hom` and `inv` are inverse. -/
  hom_inv_id : hom ≫ inv = 𝟙 (imageObj f T left)
  /-- `inv` and `hom` are inverse. -/
  inv_hom_id : inv ≫ hom = 𝟙 (imageObj f T right)
  /-- `hom` lies over the identity of `T`. -/
  hom_isHomLift : F.p.IsHomLift (𝟙 T) hom
  /-- `inv` lies over the identity of `T`. -/
  inv_isHomLift : F.p.IsHomLift (𝟙 T) inv

namespace Arrow

/-- The identity arrow on an object of `U`. -/
def id (f : Functor.ofTypeValued U ⟶ F) {T : C} (x : U.obj T) : Arrow f T where
  left := x
  right := x
  hom := 𝟙 (imageObj f T x)
  inv := 𝟙 (imageObj f T x)
  hom_inv_id := sorry
  inv_hom_id := sorry
  hom_isHomLift := sorry
  inv_isHomLift := sorry

/-- The inverse of a kernel-pair arrow. -/
def inverse {f : Functor.ofTypeValued U ⟶ F} {T : C} (a : Arrow f T) : Arrow f T where
  left := a.right
  right := a.left
  hom := a.inv
  inv := a.hom
  hom_inv_id := a.inv_hom_id
  inv_hom_id := a.hom_inv_id
  hom_isHomLift := a.inv_isHomLift
  inv_isHomLift := a.hom_isHomLift

/-- Composite of a later kernel-pair arrow with an earlier kernel-pair arrow. -/
def comp {f : Functor.ofTypeValued U ⟶ F} {T : C} (later earlier : Arrow f T)
    (h : later.right = earlier.left) : Arrow f T where
  left := later.left
  right := earlier.right
  hom := later.hom ≫ eqToHom (congrArg (imageObj f T) h) ≫ earlier.hom
  inv := earlier.inv ≫ eqToHom (congrArg (imageObj f T) h.symm) ≫ later.inv
  hom_inv_id := sorry
  inv_hom_id := sorry
  hom_isHomLift := sorry
  inv_isHomLift := sorry

/-- Transport a morphism of images in `F` along a base arrow, using the strongly cocartesian
lift of the image of the unique elements-arrow. -/
def transportHom (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T')
    {x y : U.obj T} (α : imageObj f T x ⟶ imageObj f T y)
    (hSC : F.p.IsStronglyCocartesian φ (imageLift f φ x))
    (hLift : F.p.IsHomLift φ (α ≫ imageLift f φ y)) :
    imageObj f T' (U.map φ x) ⟶ imageObj f T' (U.map φ y) :=
  @IsStronglyCocartesian.map _ _ _ _ F.p _ _ (imageObj f T x) (imageObj f T' (U.map φ x))
    φ (imageLift f φ x) hSC _ (imageObj f T' (U.map φ y)) (𝟙 T') φ
    (Category.comp_id φ).symm (α ≫ imageLift f φ y) hLift

/-- The image of a kernel-pair arrow along a morphism of `C`. -/
def map (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (a : Arrow f T) :
    Arrow f T' where
  left := U.map φ a.left
  right := U.map φ a.right
  hom := transportHom f φ a.hom sorry sorry
  inv := transportHom f φ a.inv sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry
  hom_isHomLift := sorry
  inv_isHomLift := sorry

end Arrow

/-- The Type-valued functor `R = U ×_{f, F, f} U`. -/
def relation (f : Functor.ofTypeValued U ⟶ F) : C ⥤ Type (max v w) where
  obj T := Arrow f T
  map φ := ofHom fun a ↦ Arrow.map f φ a
  map_id := sorry
  map_comp := sorry

/-- The target projection, sending an arrow to its first factor. -/
def tgt (f : Functor.ofTypeValued U ⟶ F) : relation f ⟶ U where
  app T := ofHom fun a ↦ a.left
  naturality := sorry

/-- The source projection, sending an arrow to its second factor. -/
def src (f : Functor.ofTypeValued U ⟶ F) : relation f ⟶ U where
  app T := ofHom fun a ↦ a.right
  naturality := sorry

/-- A triple of objects of `U` with composable kernel-pair isomorphisms, modelling
`U ×_F U ×_F U`. -/
structure Triple (f : Functor.ofTypeValued U ⟶ F) (T : C) where
  /-- The first factor. -/
  left : U.obj T
  /-- The middle factor. -/
  middle : U.obj T
  /-- The last factor. -/
  right : U.obj T
  /-- The isomorphism from the first image to the middle image. -/
  iso₀ : Arrow f T
  /-- The isomorphism from the middle image to the last image. -/
  iso₁ : Arrow f T
  /-- `iso₀` has first factor `left`. -/
  iso₀_left : iso₀.left = left
  /-- `iso₀` has second factor `middle`. -/
  iso₀_right : iso₀.right = middle
  /-- `iso₁` has first factor `middle`. -/
  iso₁_left : iso₁.left = middle
  /-- `iso₁` has second factor `right`. -/
  iso₁_right : iso₁.right = right

/-- The Type-valued functor of triples `U ×_{f, F, f} U ×_{f, F, f} U`. -/
def triple (f : Functor.ofTypeValued U ⟶ F) : C ⥤ Type (max v w) where
  obj T := Triple f T
  map φ := ofHom fun p ↦
    { left := U.map φ p.left
      middle := U.map φ p.middle
      right := U.map φ p.right
      iso₀ := Arrow.map f φ p.iso₀
      iso₁ := Arrow.map f φ p.iso₁
      iso₀_left := sorry
      iso₀_right := sorry
      iso₁_left := sorry
      iso₁_right := sorry }
  map_id := sorry
  map_comp := sorry

/-- Extract a composable triple from a point of the pullback of `src` against `tgt`. -/
def composableToTriple (f : Functor.ofTypeValued U ⟶ F) (T : C)
    (p : (pullback (src f) (tgt f)).obj T) : Triple f T :=
  let e := (Types.pullbackIsoPullback ((src f).app T) ((tgt f).app T)).hom
    ((pullbackObjIso (src f) (tgt f) T).hom p)
  let later : Arrow f T := e.1.1
  let earlier : Arrow f T := e.1.2
  { left := later.left
    middle := later.right
    right := earlier.right
    iso₀ := later
    iso₁ := earlier
    iso₀_left := rfl
    iso₀_right := rfl
    iso₁_left := sorry
    iso₁_right := rfl }

/-- Rebuild a pullback point from a composable triple. -/
def tripleToComposable (f : Functor.ofTypeValued U ⟶ F) (T : C)
    (p : Triple f T) : (pullback (src f) (tgt f)).obj T :=
  (pullbackObjIso (src f) (tgt f) T).inv
    ((Types.pullbackIsoPullback ((src f).app T) ((tgt f).app T)).inv
      ⟨⟨p.iso₀, p.iso₁⟩, p.iso₀_right.trans p.iso₁_left.symm⟩)

/-- The canonical isomorphism `R ×_{s, U, t} R ≅ U ×_F U ×_F U`. -/
def composableIso (f : Functor.ofTypeValued U ⟶ F) :
    pullback (src f) (tgt f) ≅ triple f where
  hom :=
    { app T := ofHom fun p ↦ composableToTriple f T p
      naturality := sorry }
  inv :=
    { app T := ofHom fun p ↦ tripleToComposable f T p
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- First-and-last projection of a triple onto a kernel-pair arrow. -/
def firstLast (f : Functor.ofTypeValued U ⟶ F) : triple f ⟶ relation f where
  app T := ofHom fun p ↦
    Arrow.comp p.iso₀ p.iso₁ (p.iso₀_right.trans p.iso₁_left.symm)
  naturality := sorry

/-- Composition of kernel-pair arrows: first-and-last projection after `composableIso`. -/
def comp (f : Functor.ofTypeValued U ⟶ F) : pullback (src f) (tgt f) ⟶ relation f :=
  (composableIso f).hom ≫ firstLast f

/-- The identity-arrow map of the kernel pair. -/
def identity (f : Functor.ofTypeValued U ⟶ F) : U ⟶ relation f where
  app T := ofHom fun x ↦ Arrow.id f x
  naturality := sorry

/-- The inverse-arrow map of the kernel pair. -/
def inverse (f : Functor.ofTypeValued U ⟶ F) : relation f ⟶ relation f where
  app T := ofHom fun a ↦ Arrow.inverse a
  naturality := sorry

end CategoryTheory.GroupoidInFunctors
