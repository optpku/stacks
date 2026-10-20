module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison for full-subcategory restriction

The identity functor preserves every object property, and its restriction is
canonically isomorphic to the identity of the corresponding full subcategory.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u} [Category.{v} C]

/-- The identity functor carries an object property into itself. -/
theorem mapsToId (P : ObjectProperty C) :
    P ≤ P.inverseImage (𝟭 C) := sorry

/-- Restriction of the identity functor is canonically isomorphic to the
identity functor on the selected full subcategory. -/
@[stacks 001D "identity comparison for full-subcategory restriction"]
def idIso (P : ObjectProperty C) :
    restrict (𝟭 C) (mapsToId P) ≅ 𝟭 P.FullSubcategory :=
  (P.fullyFaithfulι.whiskeringRight P.FullSubcategory).preimageIso
    (Iso.refl P.ι)

/-- The forward identity comparison is componentwise the identity on
underlying objects. -/
@[simp]
theorem idIso_hom_app_hom (P : ObjectProperty C)
    (X : P.FullSubcategory) :
    ((idIso P).hom.app X).hom = 𝟙 X.obj := sorry

/-- The inverse identity comparison is componentwise the identity on
underlying objects. -/
@[simp]
theorem idIso_inv_app_hom (P : ObjectProperty C)
    (X : P.FullSubcategory) :
    ((idIso P).inv.app X).hom = 𝟙 X.obj := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
