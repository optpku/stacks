module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Categories of elements from sections

A section of a type-valued functor pulled back along `p : D ⥤ C` determines a functor from `D`
to the opposite category of elements. This module owns that construction independently of any
fibredness, topology, cleavage, or based-category assumptions.
-/

@[expose] public section

universe w u v uD vD

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

namespace CategoryOfElements.Section

/-- The category-of-elements object selected at `d` by a section of `p.op ⋙ F`. -/
def element (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) (d : D) : F.Elements :=
  F.elementsMk (op (p.obj d)) (σ.1 (op d))

/-- The base object of the element selected by a section is the opposite projected object. -/
@[simp]
theorem element_fst (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) (d : D) :
    (element p F σ d).1 = op (p.obj d) := sorry

/-- The value of the element selected by a section is its component at the given object. -/
@[simp]
theorem element_snd (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) (d : D) :
    (element p F σ d).2 = σ.1 (op d) := sorry

/-- Section naturality supplies the membership equation for the category-of-elements arrow
associated to a morphism of `D`. -/
theorem map_property (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) {d e : D} (f : d ⟶ e) :
    F.map (p.map f).op (element p F σ e).2 = (element p F σ d).2 := sorry

/-- The morphism in the opposite category of elements induced by a section and a morphism of
the indexing category. -/
def hom (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) {d e : D} (f : d ⟶ e) :
    op (element p F σ d) ⟶ op (element p F σ e) :=
  Quiver.Hom.op <|
    CategoryOfElements.homMk (element p F σ e) (element p F σ d)
      (p.map f).op (map_property p F σ f)

/-- The underlying category-of-elements arrow induced by a section lies over the opposite of
the projected morphism. -/
@[simp]
theorem hom_unop_val (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) {d e : D} (f : d ⟶ e) :
    (hom p F σ f).unop.val = (p.map f).op := sorry

/-- The morphisms induced by a section preserve identities. -/
theorem hom_id (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) (d : D) :
    hom p F σ (𝟙 d) = 𝟙 (op (element p F σ d)) := sorry

/-- The morphisms induced by a section preserve composition. -/
theorem hom_comp (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) {d e k : D} (f : d ⟶ e) (g : e ⟶ k) :
    hom p F σ (f ≫ g) = hom p F σ f ≫ hom p F σ g := sorry

/-- A section of `p.op ⋙ F` as a functor from the indexing category to the opposite category
of elements of `F`. -/
def functor (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) : D ⥤ F.Elementsᵒᵖ where
  obj d := op (element p F σ d)
  map f := hom p F σ f
  map_id d := hom_id p F σ d
  map_comp f g := hom_comp p F σ f g

/-- The functor induced by a section sends an object to its selected element. -/
@[simp]
theorem functor_obj (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) (d : D) :
    (functor p F σ).obj d = op (element p F σ d) := sorry

/-- The functor induced by a section sends a morphism over the opposite projected morphism. -/
@[simp]
theorem functor_map_unop_val (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) {d e : D} (f : d ⟶ e) :
    ((functor p F σ).map f).unop.val = (p.map f).op := sorry

/-- The functor induced by a section commutes strictly with the projection to `C`. -/
@[simp]
theorem functor_comp_projection (p : D ⥤ C) (F : Cᵒᵖ ⥤ Type w)
    (σ : (p.op ⋙ F).sections) :
    functor p F σ ⋙ (CategoryOfElements.π F).leftOp = p := sorry

end CategoryOfElements.Section

end CategoryTheory
