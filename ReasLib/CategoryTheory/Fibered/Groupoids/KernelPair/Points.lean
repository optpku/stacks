/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
public import ReasLib.CategoryTheory.Fibered.Fiber.Hom
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Points of the kernel pair of a map from a presheaf

The value at a base object consists of two presheaf elements and a vertical
isomorphism between their images. Restriction factors the given isomorphism
through the actual image arrows using the supplied groupoid-fibration property.
The value universe is the morphism universe of the base, independently of its
object universe.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Bicategory

noncomputable section

universe u v w

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]

/-- The discrete Grothendieck construction, regarded as a groupoid fibration. -/
def ofPresheaf (P : Cᵒᵖ ⥤ Type w) :
    FiberedCategoryOver.Groupoids.{u, v, max u w, v} C :=
  (FiberedCategoryOver.Sets.toGroupoids C).obj
    ((FiberedCategoryOver.Sets.ofPresheaf C).obj P)

namespace PresheafKernelPair

variable (P : Cᵒᵖ ⥤ Type v)
variable {X : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}
variable (f : ofPresheaf P ⟶ X)

/-- An element of the source presheaf as its actual standard-fibre object. -/
def point (T : C) (a : P.obj (op T)) : (ofPresheaf P).p.Fiber T :=
  FiberedCategoryOver.Sets.ofPresheaf.valueToFiber P T a

/-- The image in the target fibre of an actual source element. -/
def image (T : C) (a : P.obj (op T)) : X.p.Fiber T :=
  (fiberFunctor f T).obj (point P T a)

/-- A kernel-pair point records its two source points and their given vertical isomorphism. -/
structure Point (T : C) where
  fst : P.obj (op T)
  snd : P.obj (op T)
  iso : image P f T fst ≅ image P f T snd

/-- The actual source arrow from a restricted presheaf element to the original element. -/
def pointArrow {T T' : C} (k : T' ⟶ T) (a : P.obj (op T)) :
    (point P T' (P.map k.op a)).1 ⟶ (point P T a).1 :=
  (CategoryOfElements.homMk
    (⟨op T, a⟩ : P.Elements)
    (⟨op T', P.map k.op a⟩ : P.Elements) k.op rfl).op

/-- The target arrow is the literal image of the displayed presheaf restriction arrow. -/
def imageArrow {T T' : C} (k : T' ⟶ T) (a : P.obj (op T)) :
    (image P f T' (P.map k.op a)).1 ⟶ (image P f T a).1 :=
  (toFunctor f).map (pointArrow P k a)

/-- Composing the first restriction arrow with a vertical target map lies over
the same base arrow as the second restriction arrow. -/
theorem imageArrow_comp_isHomLift {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ⟶ image P f T b) :
    X.p.IsHomLift (X.p.map (imageArrow P f k b))
      (imageArrow P f k a ≫ α.1) := sorry

/-- The factor through the second restriction arrow is vertical over the restricted base. -/
theorem restrictionHom_isHomLift {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ⟶ image P f T b) :
    let sourceArrow := imageArrow P f k a
    let targetArrow := imageArrow P f k b
    letI : X.p.IsCartesian (X.p.map targetArrow) targetArrow :=
      Functor.IsFibered.InGroupoids.all_isCartesian targetArrow
    letI : X.p.IsHomLift (X.p.map targetArrow) (sourceArrow ≫ α.1) :=
      imageArrow_comp_isHomLift P f k a b α
    X.p.IsHomLift (𝟙 T')
      (Functor.IsCartesian.map X.p (X.p.map targetArrow) targetArrow
        (sourceArrow ≫ α.1)) := sorry

/-- Pull a specified vertical map through the actual target restriction arrow.
The Cartesian universal property is a field of the supplied target fibration. -/
def restrictionHom {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ⟶ image P f T b) :
    image P f T' (P.map k.op a) ⟶ image P f T' (P.map k.op b) := by
  let sourceArrow := imageArrow P f k a
  let targetArrow := imageArrow P f k b
  letI : X.p.IsCartesian (X.p.map targetArrow) targetArrow :=
    Functor.IsFibered.InGroupoids.all_isCartesian targetArrow
  letI : X.p.IsHomLift (X.p.map targetArrow) (sourceArrow ≫ α.1) :=
    imageArrow_comp_isHomLift P f k a b α
  exact Functor.Fiber.Hom.mk
    (Functor.IsCartesian.map X.p (X.p.map targetArrow) targetArrow
      (sourceArrow ≫ α.1))
    (restrictionHom_isHomLift P f k a b α)

/-- Restriction preserves both given directions of a vertical isomorphism. -/
def restrictionIso {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ≅ image P f T b) :
    image P f T' (P.map k.op a) ≅ image P f T' (P.map k.op b) where
  hom := restrictionHom P f k a b α.hom
  inv := restrictionHom P f k b a α.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restrict the two displayed points and their given comparison. -/
def restrict {T T' : C} (k : T' ⟶ T) (a : Point P f T) : Point P f T' where
  fst := P.map k.op a.fst
  snd := P.map k.op a.snd
  iso := restrictionIso P f k a.fst a.snd a.iso

/-- Identity restriction fixes a kernel-pair point. -/
theorem restrict_id (T : C) (a : Point P f T) :
    restrict P f (𝟙 T) a = a := sorry

/-- Restriction of a kernel-pair point is contravariantly functorial. -/
theorem restrict_comp {T T' T'' : C} (k : T' ⟶ T) (l : T'' ⟶ T')
    (a : Point P f T) :
    restrict P f (l ≫ k) a = restrict P f l (restrict P f k a) := sorry

/-- The correctly sized presheaf of actual points and vertical isomorphisms of the kernel pair. -/
def presheaf : Cᵒᵖ ⥤ Type v where
  obj T := Point P f (unop T)
  map k := TypeCat.ofHom (restrict P f k.unop)
  map_id := by
    intro T
    ext a
    exact restrict_id P f (unop T) a
  map_comp := by
    intro T T' T'' k l
    ext a
    exact restrict_comp P f k.unop l.unop a

/-- The first projection is the first recorded presheaf element. -/
def fst : presheaf P f ⟶ P where
  app T := TypeCat.ofHom (fun a ↦ a.fst)
  naturality := sorry

/-- The second projection is the second recorded presheaf element. -/
def snd : presheaf P f ⟶ P where
  app T := TypeCat.ofHom (fun a ↦ a.snd)
  naturality := sorry

/-- The diagonal stores the same point twice and its literal identity isomorphism. -/
def diagonal : P ⟶ presheaf P f where
  app T := TypeCat.ofHom (fun a ↦ ⟨a, a, Iso.refl _⟩)
  naturality := sorry

end PresheafKernelPair
end CategoryTheory.FiberedCategoryOver.Groupoids
