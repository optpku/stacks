/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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

/-- The homotopy `1`-category of a bicategory. It has the same objects as `B`, while a morphism
from `X` to `Y` is a connected component of the hom-category `X ⟶ Y`.

This is the reusable homwise `π₀` truncation. Associators and unitors become equalities after
passing to connected components. -/
@[ext, stacks 04SC "homotopy category of a bicategory"]
structure HomotopyCategory (B : Type u) where
  /-- The underlying object of the bicategory. -/
  as : B

namespace HomotopyCategory

variable {B : Type u} [Bicategory.{w, v} B]

section CategoryImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The underlying quiver of the homotopy `1`-category. -/
private instance categoryStruct : CategoryStruct.{v} (HomotopyCategory B) where
  Hom X Y := ConnectedComponents (X.as ⟶ Y.as)
  id X := ConnectedComponents.mk (𝟙 X.as)
  comp f g := Quotient.map₂ (fun f g ↦ f ≫ g)
    (fun _ _ hf _ _ hg ↦ Bicategory.Zigzag.comp hf hg) f g

/-- Identity components are left identities in the homotopy `1`-category. -/
private theorem id_comp {X Y : HomotopyCategory B} (f : X ⟶ Y) :
    𝟙 X ≫ f = f := sorry

/-- Identity components are right identities in the homotopy `1`-category. -/
private theorem comp_id {X Y : HomotopyCategory B} (f : X ⟶ Y) :
    f ≫ 𝟙 Y = f := sorry

/-- Composition of components is associative in the homotopy `1`-category. -/
private theorem assoc
    {W X Y Z : HomotopyCategory B} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := sorry

end Implementation

/-- The category structure on the homwise `π₀` of a bicategory. -/
instance category : Category.{v} (HomotopyCategory B) where
  toCategoryStruct := Implementation.categoryStruct
  id_comp := Implementation.id_comp
  comp_id := Implementation.comp_id
  assoc := Implementation.assoc

end CategoryImplementation

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
