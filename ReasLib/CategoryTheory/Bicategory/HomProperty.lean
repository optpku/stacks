/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Hom properties in a bicategory

A `Bicategory.HomProperty` selects `1`-morphisms between the images of an object family.
The pair-indexed presentation distinguishes chosen objects even when they have equal ambient
images. `HomProperty.IsMultiplicative` is the closure needed to form a locally induced
bicategory, but is useful independently for closure arguments.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u'

namespace Bicategory

variable {B : Type u'}

/-- A property of `1`-morphisms between the images of a family of objects in a bicategory.

This is the bicategorical analogue of `MorphismProperty`. The pair-indexed form is intentional:
it can distinguish chosen objects that `F` sends to the same ambient object, and its
multiplicativity condition below does not require the ambient bicategory to be strict. Each
`Q X Y` is still an ordinary mathlib `ObjectProperty`, so its hom category is supplied by
`ObjectProperty.FullSubcategory`. -/
@[stacks 0040 "bicategorical hom property"]
abbrev HomProperty {C : Type u} [Bicategory.{w, v} C] (F : B → C) :=
  (X Y : B) → ObjectProperty (F X ⟶ F Y)

namespace HomProperty

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C} (Q : HomProperty F)

/-- A bicategorical hom property is multiplicative when it contains identity `1`-morphisms and
is closed under horizontal composition. -/
@[stacks 0040 "multiplicative bicategorical hom property"]
class IsMultiplicative : Prop where
  /-- Identity `1`-morphisms satisfy the hom property. -/
  id_mem (X : B) : Q X X (𝟙 (F X))
  /-- Composites of `1`-morphisms satisfying the hom property again satisfy it. -/
  comp_mem {X Y Z : B} {f : F X ⟶ F Y} {g : F Y ⟶ F Z} :
    Q X Y f → Q Y Z g → Q X Z (f ≫ g)

/-- A bicategorical hom property is closed under isomorphisms when each selected hom property
is closed under isomorphisms in its ambient hom category.

This packages the pair-indexed family of `ObjectProperty.IsClosedUnderIsomorphisms` instances
as one reusable assumption, mirroring mathlib's bundled object-property API. -/
class IsClosedUnderIsomorphisms : Prop where
  /-- Closure under isomorphisms for the selected hom category from `X` to `Y`. -/
  isClosedUnderIsomorphisms (X Y : B) :
    (Q X Y).IsClosedUnderIsomorphisms

attribute [instance] IsClosedUnderIsomorphisms.isClosedUnderIsomorphisms

/-- A morphism satisfying a bicategorical hom property remains satisfying it after an
isomorphism in the selected ambient hom category. -/
lemma prop_of_iso [Q.IsClosedUnderIsomorphisms]
    {X Y : B} {f g : F X ⟶ F Y} (e : f ≅ g) (hf : Q X Y f) : Q X Y g := sorry

/-- Membership in a bicategorical hom property is invariant under an ambient hom-category
isomorphism. -/
lemma prop_iff_of_iso [Q.IsClosedUnderIsomorphisms]
    {X Y : B} {f g : F X ⟶ F Y} (e : f ≅ g) : Q X Y f ↔ Q X Y g := sorry

/-- A bicategorical hom property is transported along an isomorphism-valued `IsIso` cell. -/
lemma prop_of_isIso [Q.IsClosedUnderIsomorphisms]
    {X Y : B} {f g : F X ⟶ F Y} (e : f ⟶ g) [IsIso e] (hf : Q X Y f) : Q X Y g := sorry

/-- Membership in a bicategorical hom property is invariant under an isomorphism-valued
`IsIso` cell. -/
lemma prop_iff_of_isIso [Q.IsClosedUnderIsomorphisms]
    {X Y : B} {f g : F X ⟶ F Y} (e : f ⟶ g) [IsIso e] : Q X Y f ↔ Q X Y g := sorry

/-- Identity `1`-morphisms belong to a multiplicative bicategorical hom property. -/
lemma id_mem [Q.IsMultiplicative] (X : B) : Q X X (𝟙 (F X)) := sorry
/- Proof strategy: apply the class field `IsMultiplicative.id_mem X`. -/

/-- A multiplicative bicategorical hom property is closed under horizontal composition. -/
lemma comp_mem [Q.IsMultiplicative]
    {X Y Z : B} {f : F X ⟶ F Y} {g : F Y ⟶ F Z}
    (hf : Q X Y f) (hg : Q Y Z g) : Q X Z (f ≫ g) := sorry
/- Proof strategy: apply the class field `IsMultiplicative.comp_mem hf hg`. -/

end HomProperty

end Bicategory

end CategoryTheory
