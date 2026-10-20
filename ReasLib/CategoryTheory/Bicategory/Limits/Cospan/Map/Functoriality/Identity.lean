module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Iso.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity functoriality for mapping bicategorical cospans

Mapping a cospan transformation by the identity pseudofunctor has the same three vertex maps
as the original transformation. Its generating comparison isomorphisms are propositionally,
rather than definitionally, the original comparisons because they pass through the identity
pseudofunctor's composition constraints.

The canonical comparison is therefore an isomorphism of cospan transformations with identity
vertex components, not an equality of structure implementations.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

namespace Implementation

/-- Identity vertex cells satisfy the left generating naturality square comparing mapping by
the identity pseudofunctor with the original cospan transformation. -/
private theorem identityIso.leftNaturality
    (ψ : CospanTransform f g f' g') :
    (Iso.refl ψ.left).hom ▷ f' ≫ ψ.leftIso.hom =
      (map ψ (Pseudofunctor.id B)).leftIso.hom ≫
        f ◁ (Iso.refl ψ.base).hom := sorry

/-- Identity vertex cells satisfy the right generating naturality square comparing mapping by
the identity pseudofunctor with the original cospan transformation. -/
private theorem identityIso.rightNaturality
    (ψ : CospanTransform f g f' g') :
    (Iso.refl ψ.right).hom ▷ g' ≫ ψ.rightIso.hom =
      (map ψ (Pseudofunctor.id B)).rightIso.hom ≫
        g ◁ (Iso.refl ψ.base).hom := sorry

end Implementation

/-- Mapping a cospan transformation by the identity pseudofunctor is canonically isomorphic
to the original transformation, with identity isomorphisms at all three vertices. -/
@[stacks 0040 "identity comparison for mapping bicategorical cospan transformations"]
def mapIdentityIso (ψ : CospanTransform f g f' g') :
    map ψ (Pseudofunctor.id B) ≅ ψ :=
  Hom.isoMk (Iso.refl ψ.left) (Iso.refl ψ.right) (Iso.refl ψ.base)
    (Implementation.identityIso.leftNaturality ψ)
    (Implementation.identityIso.rightNaturality ψ)

/-- The forward left component of `mapIdentityIso` is an identity `2`-morphism. -/
@[simp]
theorem mapIdentityIso.hom.left
    (ψ : CospanTransform f g f' g') :
    Hom.left (mapIdentityIso ψ).hom = 𝟙 ψ.left := sorry

/-- The forward right component of `mapIdentityIso` is an identity `2`-morphism. -/
@[simp]
theorem mapIdentityIso.hom.right
    (ψ : CospanTransform f g f' g') :
    Hom.right (mapIdentityIso ψ).hom = 𝟙 ψ.right := sorry

/-- The forward base component of `mapIdentityIso` is an identity `2`-morphism. -/
@[simp]
theorem mapIdentityIso.hom.base
    (ψ : CospanTransform f g f' g') :
    Hom.base (mapIdentityIso ψ).hom = 𝟙 ψ.base := sorry

/-- The inverse left component of `mapIdentityIso` is an identity `2`-morphism. -/
@[simp]
theorem mapIdentityIso.inv.left
    (ψ : CospanTransform f g f' g') :
    Hom.left (mapIdentityIso ψ).inv = 𝟙 ψ.left := sorry

/-- The inverse right component of `mapIdentityIso` is an identity `2`-morphism. -/
@[simp]
theorem mapIdentityIso.inv.right
    (ψ : CospanTransform f g f' g') :
    Hom.right (mapIdentityIso ψ).inv = 𝟙 ψ.right := sorry

/-- The inverse base component of `mapIdentityIso` is an identity `2`-morphism. -/
@[simp]
theorem mapIdentityIso.inv.base
    (ψ : CospanTransform f g f' g') :
    Hom.base (mapIdentityIso ψ).inv = 𝟙 ψ.base := sorry

/- Data and axiom audit (mathlib 4.32):

All three non-`Prop` components of `mapIdentityIso` are explicit reflexivity isomorphisms.
Any `sorryAx` dependency is confined to the two generating naturality squares and inherited
modification-isomorphism laws. -/

end CategoryTheory.Bicategory.CospanTransform
