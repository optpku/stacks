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

/-- Two points agree when their component identifications commute with their isomorphisms. -/
theorem Point.ext {T : C} (a b : Point P f T)
    (hfst : a.fst = b.fst) (hsnd : a.snd = b.snd)
    (hiso : eqToHom (congrArg (image P f T) hfst) ≫ b.iso.hom =
      a.iso.hom ≫ eqToHom (congrArg (image P f T) hsnd)) : a = b := by
  cases a
  cases b
  dsimp only at hfst hsnd hiso ⊢
  cases hfst
  cases hsnd
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hiso
  congr 1
  exact Iso.ext hiso.symm

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

/-- The image of the displayed restriction arrow still lies over its given base arrow. -/
theorem imageArrow_isHomLift {T T' : C} (k : T' ⟶ T) (a : P.obj (op T)) :
    X.p.IsHomLift k (imageArrow P f k a) := by
  letI : (ofPresheaf P).p.IsHomLift k (pointArrow P k a) :=
    Functor.IsHomLift.map (pointArrow P k a)
  exact BasedFunctor.preserves_isHomLift (toBasedFunctor f) k (pointArrow P k a)

/-- The identity image arrow is the transport given by the presheaf identity law. -/
theorem imageArrow_id (T : C) (a : P.obj (op T))
    (h : P.map (𝟙 T).op a = a) :
    imageArrow P f (𝟙 T) a = (eqToHom (congrArg (image P f T) h)).1 := by
  have hp : pointArrow P (𝟙 T) a =
      eqToHom (congrArg (fun b ↦ (point P T b).1) h) := by
    apply ((CategoryOfElements.π P).leftOp).map_injective
    change (𝟙 T) = ((CategoryOfElements.π P).leftOp).map
      (eqToHom (congrArg (fun b ↦ (point P T b).1) h))
    rw [eqToHom_map]
    rfl
  change (toFunctor f).map (pointArrow P (𝟙 T) a) =
    (Functor.Fiber.fiberInclusion : X.p.Fiber T ⥤ X.total).map
      (eqToHom (congrArg (image P f T) h))
  simp only [hp, eqToHom_map]
  rfl

/-- Image arrows compose after the transport given by the presheaf composition law. -/
theorem imageArrow_comp {T T' T'' : C} (k : T' ⟶ T) (l : T'' ⟶ T')
    (a : P.obj (op T)) (h : P.map (l ≫ k).op a = P.map l.op (P.map k.op a)) :
    imageArrow P f (l ≫ k) a = (eqToHom (congrArg (image P f T'') h)).1 ≫
      imageArrow P f l (P.map k.op a) ≫ imageArrow P f k a := by
  have hp : pointArrow P (l ≫ k) a =
      eqToHom (congrArg (fun b ↦ (point P T'' b).1) h) ≫
        pointArrow P l (P.map k.op a) ≫ pointArrow P k a := by
    apply ((CategoryOfElements.π P).leftOp).map_injective
    erw [((CategoryOfElements.π P).leftOp).map_comp,
      ((CategoryOfElements.π P).leftOp).map_comp, eqToHom_map]
    change l ≫ k = (𝟙 T'') ≫ l ≫ k
    simp
  change (toFunctor f).map (pointArrow P (l ≫ k) a) =
    (Functor.Fiber.fiberInclusion : X.p.Fiber T'' ⥤ X.total).map
        (eqToHom (congrArg (image P f T'') h)) ≫
      (toFunctor f).map (pointArrow P l (P.map k.op a)) ≫
        (toFunctor f).map (pointArrow P k a)
  simp only [hp, Functor.map_comp, eqToHom_map]
  rfl

/-- Composing the first restriction arrow with a vertical target map lies over
the same base arrow as the second restriction arrow. -/
theorem imageArrow_comp_isHomLift {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ⟶ image P f T b) :
    X.p.IsHomLift (X.p.map (imageArrow P f k b))
      (imageArrow P f k a ≫ α.1) := by
  letI := imageArrow_isHomLift P f k a
  letI := α.2
  have h : X.p.IsHomLift k (imageArrow P f k a ≫ α.1) := inferInstance
  have rebase {R S : C} {x y z : X.total} (g : R ⟶ S)
      (φ : y ⟶ z) (ψ : x ⟶ z) (hφ : X.p.IsHomLift g φ)
      (hψ : X.p.IsHomLift g ψ) : X.p.IsHomLift (X.p.map φ) ψ := by
    cases hφ
    exact hψ
  exact rebase k _ _ (imageArrow_isHomLift P f k b) h

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
        (sourceArrow ≫ α.1)) := by
  dsimp only
  letI := imageArrow_comp_isHomLift P f k a b α
  let χ := Functor.IsCartesian.map X.p (X.p.map (imageArrow P f k b))
    (imageArrow P f k b) (imageArrow P f k a ≫ α.1)
  exact Eq.mp (congrArg (fun U ↦ X.p.IsHomLift (𝟙 U) χ)
    (image P f T' (P.map k.op b)).2)
    (Functor.IsCartesian.map_isHomLift X.p (X.p.map (imageArrow P f k b))
      (imageArrow P f k b) (imageArrow P f k a ≫ α.1))

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

/-- The restricted map makes the square of the two actual image arrows commute. -/
theorem restrictionHom_fac {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ⟶ image P f T b) :
    (restrictionHom P f k a b α).1 ≫ imageArrow P f k b =
      imageArrow P f k a ≫ α.1 := by
  letI := imageArrow_comp_isHomLift P f k a b α
  exact Functor.IsCartesian.fac X.p (X.p.map (imageArrow P f k b))
    (imageArrow P f k b) (imageArrow P f k a ≫ α.1)

/-- A vertical map is determined by its square with the second restriction arrow. -/
theorem restrictionHom_unique {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ⟶ image P f T b)
    (β : image P f T' (P.map k.op a) ⟶ image P f T' (P.map k.op b))
    (hβ : β.1 ≫ imageArrow P f k b = imageArrow P f k a ≫ α.1) :
    β = restrictionHom P f k a b α := by
  apply Functor.Fiber.hom_ext
  change β.1 = (restrictionHom P f k a b α).1
  letI := imageArrow_comp_isHomLift P f k a b α
  letI : X.p.IsHomLift (𝟙 (X.p.obj (image P f T' (P.map k.op b)).1)) β.1 :=
    (image P f T' (P.map k.op b)).2.symm ▸ β.2
  exact Functor.IsCartesian.map_uniq X.p (X.p.map (imageArrow P f k b))
    (imageArrow P f k b) (imageArrow P f k a ≫ α.1) β.1 hβ

/-- Restricting a vertical identity gives the vertical identity. -/
theorem restrictionHom_id {T T' : C} (k : T' ⟶ T) (a : P.obj (op T)) :
    restrictionHom P f k a a (𝟙 (image P f T a)) =
      𝟙 (image P f T' (P.map k.op a)) := by
  symm
  apply restrictionHom_unique
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  simp

/-- Restriction preserves composition of vertical maps. -/
theorem restrictionHom_comp {T T' : C} (k : T' ⟶ T)
    (a b c : P.obj (op T)) (α : image P f T a ⟶ image P f T b)
    (β : image P f T b ⟶ image P f T c) :
    restrictionHom P f k a c (α ≫ β) =
      restrictionHom P f k a b α ≫ restrictionHom P f k b c β := by
  symm
  apply restrictionHom_unique
  change ((restrictionHom P f k a b α).1 ≫ (restrictionHom P f k b c β).1) ≫
      imageArrow P f k c = imageArrow P f k a ≫ (α.1 ≫ β.1)
  rw [Category.assoc, restrictionHom_fac, ← Category.assoc, restrictionHom_fac,
    Category.assoc]

/-- A vertical map is determined by its composite with any arrow in a groupoid fibration. -/
theorem fiberHom_ext {T : C} {x y : X.p.Fiber T} {z : X.total}
    (α β : x ⟶ y) (φ : y.1 ⟶ z) (h : α.1 ≫ φ = β.1 ≫ φ) : α = β := by
  apply Functor.Fiber.hom_ext
  letI : X.p.IsHomLift (𝟙 (X.p.obj y.1)) α.1 := y.2.symm ▸ α.2
  letI : X.p.IsHomLift (𝟙 (X.p.obj y.1)) β.1 := y.2.symm ▸ β.2
  exact Functor.IsCartesian.ext X.p (X.p.map φ) φ α.1 β.1 h

/-- Restriction preserves both given directions of a vertical isomorphism. -/
def restrictionIso {T T' : C} (k : T' ⟶ T)
    (a b : P.obj (op T)) (α : image P f T a ≅ image P f T b) :
    image P f T' (P.map k.op a) ≅ image P f T' (P.map k.op b) where
  hom := restrictionHom P f k a b α.hom
  inv := restrictionHom P f k b a α.inv
  hom_inv_id := by
    rw [← restrictionHom_comp, α.hom_inv_id, restrictionHom_id]
  inv_hom_id := by
    rw [← restrictionHom_comp, α.inv_hom_id, restrictionHom_id]

/-- Restrict the two displayed points and their given comparison. -/
def restrict {T T' : C} (k : T' ⟶ T) (a : Point P f T) : Point P f T' where
  fst := P.map k.op a.fst
  snd := P.map k.op a.snd
  iso := restrictionIso P f k a.fst a.snd a.iso

/-- Identity restriction fixes a kernel-pair point. -/
theorem restrict_id (T : C) (a : Point P f T) :
    restrict P f (𝟙 T) a = a := by
  have ha : P.map (𝟙 T).op a.fst = a.fst := by simp
  have hb : P.map (𝟙 T).op a.snd = a.snd := by simp
  apply Point.ext P f _ _ ha hb
  apply Functor.Fiber.hom_ext
  change (eqToHom (congrArg (image P f T) ha)).1 ≫ a.iso.hom.1 =
    (restrictionHom P f (𝟙 T) a.fst a.snd a.iso.hom).1 ≫
      (eqToHom (congrArg (image P f T) hb)).1
  rw [← imageArrow_id P f T a.fst ha, ← imageArrow_id P f T a.snd hb,
    restrictionHom_fac]

/-- Restriction of a kernel-pair point is contravariantly functorial. -/
theorem restrict_comp {T T' T'' : C} (k : T' ⟶ T) (l : T'' ⟶ T')
    (a : Point P f T) :
    restrict P f (l ≫ k) a = restrict P f l (restrict P f k a) := by
  rcases a with ⟨a, b, α⟩
  have ha : P.map (l ≫ k).op a = P.map l.op (P.map k.op a) := by simp
  have hb : P.map (l ≫ k).op b = P.map l.op (P.map k.op b) := by simp
  apply Point.ext P f _ _ ha hb
  apply fiberHom_ext (φ := imageArrow P f l (P.map k.op b) ≫ imageArrow P f k b)
  change ((eqToHom (congrArg (image P f T'') ha)).1 ≫
      (restrictionHom P f l (P.map k.op a) (P.map k.op b)
        (restrictionHom P f k a b α.hom)).1) ≫
      (imageArrow P f l (P.map k.op b) ≫ imageArrow P f k b) =
    ((restrictionHom P f (l ≫ k) a b α.hom).1 ≫
      (eqToHom (congrArg (image P f T'') hb)).1) ≫
      (imageArrow P f l (P.map k.op b) ≫ imageArrow P f k b)
  calc
    _ = ((eqToHom (congrArg (image P f T'') ha)).1 ≫
        imageArrow P f l (P.map k.op a) ≫ imageArrow P f k a) ≫ α.hom.1 := by
      rw [Category.assoc, ← Category.assoc _ (imageArrow P f l (P.map k.op b)),
        restrictionHom_fac, Category.assoc, restrictionHom_fac]
      simp only [Category.assoc]
    _ = imageArrow P f (l ≫ k) a ≫ α.hom.1 := by
      rw [← imageArrow_comp P f k l a ha]
    _ = (restrictionHom P f (l ≫ k) a b α.hom).1 ≫ imageArrow P f (l ≫ k) b :=
      (restrictionHom_fac P f (l ≫ k) a b α.hom).symm
    _ = _ := by
      rw [imageArrow_comp P f k l b hb]
      simp only [Category.assoc]

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
  naturality := by
    intro T T' k
    rfl

/-- The second projection is the second recorded presheaf element. -/
def snd : presheaf P f ⟶ P where
  app T := TypeCat.ofHom (fun a ↦ a.snd)
  naturality := by
    intro T T' k
    rfl

/-- The diagonal stores the same point twice and its literal identity isomorphism. -/
def diagonal : P ⟶ presheaf P f where
  app T := TypeCat.ofHom (fun a ↦ ⟨a, a, Iso.refl _⟩)
  naturality := by
    intro T T' k
    ext a
    change (Point.mk (P.map k a) (P.map k a) (Iso.refl _)) =
      Point.mk (P.map k a) (P.map k a) (restrictionIso P f k.unop a a (Iso.refl _))
    congr 1
    apply Iso.ext
    exact (restrictionHom_id P f k.unop a).symm

end PresheafKernelPair
end CategoryTheory.FiberedCategoryOver.Groupoids
