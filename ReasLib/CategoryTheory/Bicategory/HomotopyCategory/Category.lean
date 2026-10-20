module

public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.CategoryTheory.Bicategory.Zigzag
public import ReasLib.CategoryTheory.ConnectedComponents
import Mathlib.Tactic.CrossRefAttribute

/-!
# The homotopy category of a bicategory

The homotopy `1`-category keeps the objects of a bicategory and takes connected components of
each hom-category. This file contains only the category and its representative API.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open scoped Bicategory

namespace Bicategory

namespace HomotopyCategory

/-- An object of the homotopy category records an object of the bicategory. -/
structure Obj (B : Type u) where
  /-- The underlying object of the bicategory. -/
  as : B

variable {B : Type u} [Bicategory.{w, v} B]

/-- Morphisms of the homotopy category are connected components of hom-categories. -/
def Hom (X Y : Obj B) : Type v := ConnectedComponents (X.as ⟶ Y.as)

/-- The identity component is represented by the identity `1`-morphism. -/
def id (X : Obj B) : Hom X X := ConnectedComponents.mk (𝟙 X.as)

/-- Composition of components is induced by horizontal composition of `1`-morphisms. -/
def comp {X Y Z : Obj B} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quotient.map₂ (fun f g ↦ f ≫ g)
    (fun _ _ hf _ _ hg ↦ Bicategory.Zigzag.comp hf hg) f g

section CategoryImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Identity components are left identities in the homotopy `1`-category. -/
private theorem id_comp {X Y : Obj B} (f : Hom X Y) :
    comp (id X) f = f := sorry

/-- Identity components are right identities in the homotopy `1`-category. -/
private theorem comp_id {X Y : Obj B} (f : Hom X Y) :
    comp f (id Y) = f := sorry

/-- Composition of components is associative in the homotopy `1`-category. -/
private theorem assoc
    {W X Y Z : Obj B} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Implementation

/-- The category on the objects of a bicategory with homwise connected-component morphisms. -/
def category (B : Type u) [Bicategory.{w, v} B] : Cat.{v, u} :=
  ⟨Obj B, {
    Hom := Hom
    id := id
    comp := comp
    id_comp := Implementation.id_comp
    comp_id := Implementation.comp_id
    assoc := Implementation.assoc
  }⟩

end CategoryImplementation

end HomotopyCategory

/-- The homotopy `1`-category of a bicategory has the same objects and connected components
of its hom-categories as morphisms. Associators and unitors become equalities. -/
@[stacks 04SC "homotopy category of a bicategory"]
abbrev HomotopyCategory (B : Type u) [Bicategory.{w, v} B] : Type u :=
  HomotopyCategory.category B

namespace HomotopyCategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- Regard an object of the bicategory as an object of its homotopy category. -/
def mk (X : B) : HomotopyCategory B := Obj.mk X

/-- The underlying object of the bicategory represented by a homotopy-category object. -/
abbrev as (X : HomotopyCategory B) : B := Obj.as X

/-- Objects of the homotopy category are equal when their underlying objects are equal. -/
@[ext]
theorem ext {X Y : HomotopyCategory B} (h : X.as = Y.as) : X = Y :=
by
  cases X
  cases Y
  cases h
  rfl

/-- Rewrapping the underlying object of a homotopy-category object recovers that object. -/
@[simp]
theorem mk_as (X : HomotopyCategory B) : HomotopyCategory.mk X.as = X := sorry

/-- The morphism of the homotopy `1`-category represented by a `1`-morphism of `B`. -/
@[stacks 04SC "represented morphism in the homotopy category"]
def mkHom {X Y : B} (f : X ⟶ Y) :
    HomotopyCategory.mk X ⟶ HomotopyCategory.mk Y :=
  ConnectedComponents.mk f

namespace mkHom

/-- Equality of represented morphisms is exactly zigzag-connectedness in the hom-category. -/
theorem eq_iff_zigzag {X Y : B} {f g : X ⟶ Y} :
    mkHom f = mkHom g ↔ Zigzag f g := sorry

/-- Zigzag-connected `1`-morphisms represent the same homotopy-category morphism. -/
theorem eq_of_zigzag {X Y : B} {f g : X ⟶ Y} (h : Zigzag f g) :
    mkHom f = mkHom g := sorry

/-- A `2`-morphism identifies its source and target in the homotopy `1`-category. -/
theorem eq_of_hom {X Y : B} {f g : X ⟶ Y} (eta : f ⟶ g) :
    mkHom f = mkHom g := sorry

/-- The class represented by an identity is the identity class. -/
@[simp]
theorem id (X : B) : mkHom (𝟙 X) = 𝟙 (HomotopyCategory.mk X) := sorry

/-- Taking the represented class preserves horizontal composition. -/
@[simp]
theorem comp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mkHom (f ≫ g) = mkHom f ≫ mkHom g := sorry

/-- Every morphism of the homotopy category has a representative in the corresponding
hom-category of the bicategory. -/
theorem surjective (X Y : HomotopyCategory B) :
    Function.Surjective (fun f : X.as ⟶ Y.as ↦ (mkHom f : X ⟶ Y)) := sorry

/-- To prove a property of homotopy-category morphisms, it suffices to prove it on represented
`1`-morphisms. -/
@[elab_as_elim]
theorem induction
    {motive : ∀ {X Y : HomotopyCategory B}, (X ⟶ Y) → Prop}
    {X Y : HomotopyCategory B} (f : X ⟶ Y)
    (mk : ∀ {A A' : B} (g : A ⟶ A'), motive (mkHom g)) :
    motive f := sorry

end mkHom

end HomotopyCategory

end Bicategory

end CategoryTheory
