module

public import ReasLib.CategoryTheory.Functor.Exactness.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of exact-functor composition

Composition of bundled exact functors acts on natural transformations by
left whiskering, right whiskering, and horizontal composition.  This file
provides those 2-cell operations without exposing the full-subcategory
constructor used to bundle them.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory.ExactFunctor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/-- Left whiskering of a morphism of bundled exact functors. -/
@[stacks 015F "left whiskering of exact natural transformations"]
def whiskerLeft (F : A ⥤ₑ B) {G H : B ⥤ₑ C} (β : G ⟶ H) :
    F.comp G ⟶ F.comp H :=
  ObjectProperty.homMk (P := exactFunctor A C)
    (Functor.whiskerLeft F.obj β.hom)

/-- Right whiskering of a morphism of bundled exact functors. -/
@[stacks 015F "right whiskering of exact natural transformations"]
def whiskerRight {F G : A ⥤ₑ B} (α : F ⟶ G) (H : B ⥤ₑ C) :
    F.comp H ⟶ G.comp H :=
  ObjectProperty.homMk (P := exactFunctor A C)
    (Functor.whiskerRight α.hom H.obj)

/-- Horizontal composition of morphisms of bundled exact functors. -/
@[stacks 015F "horizontal composition of exact natural transformations"]
def hcomp {F G : A ⥤ₑ B} (α : F ⟶ G)
    {H I : B ⥤ₑ C} (β : H ⟶ I) : F.comp H ⟶ G.comp I :=
  ObjectProperty.homMk (P := exactFunctor A C)
    (NatTrans.hcomp α.hom β.hom)

/-- The underlying natural transformation of exact left whiskering is
ordinary left whiskering. -/
@[simp]
theorem whiskerLeft_hom (F : A ⥤ₑ B) {G H : B ⥤ₑ C} (β : G ⟶ H) :
    (whiskerLeft F β).hom = Functor.whiskerLeft F.obj β.hom := sorry

/-- The underlying natural transformation of exact right whiskering is
ordinary right whiskering. -/
@[simp]
theorem whiskerRight_hom {F G : A ⥤ₑ B} (α : F ⟶ G) (H : B ⥤ₑ C) :
    (whiskerRight α H).hom = Functor.whiskerRight α.hom H.obj := sorry

/-- The underlying natural transformation of exact horizontal composition
is ordinary horizontal composition. -/
@[simp]
theorem hcomp_hom {F G : A ⥤ₑ B} (α : F ⟶ G)
    {H I : B ⥤ₑ C} (β : H ⟶ I) :
    (hcomp α β).hom = NatTrans.hcomp α.hom β.hom := sorry

/-- Horizontal composition factors through right and then left
whiskering. -/
theorem hcomp_eq {F G : A ⥤ₑ B} (α : F ⟶ G)
    {H I : B ⥤ₑ C} (β : H ⟶ I) :
    hcomp α β = whiskerRight α H ≫ whiskerLeft G β := sorry

/-- Horizontal composition preserves identity transformations. -/
@[simp]
theorem hcomp_id (F : A ⥤ₑ B) (G : B ⥤ₑ C) :
    hcomp (𝟙 F) (𝟙 G) = 𝟙 (F.comp G) := sorry

/-- Horizontal composition satisfies the interchange law with vertical
composition. -/
theorem hcomp_comp {F₁ F₂ F₃ : A ⥤ₑ B}
    (α₁ : F₁ ⟶ F₂) (α₂ : F₂ ⟶ F₃)
    {G₁ G₂ G₃ : B ⥤ₑ C}
    (β₁ : G₁ ⟶ G₂) (β₂ : G₂ ⟶ G₃) :
    hcomp (α₁ ≫ α₂) (β₁ ≫ β₂) =
      hcomp α₁ β₁ ≫ hcomp α₂ β₂ := sorry

end CategoryTheory.ExactFunctor
