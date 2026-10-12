/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Comma.Over.FullyFaithful
public import ReasLib.CategoryTheory.RepresentablePresheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Elements of a representable presheaf and slices

The opposite category of elements of a representable presheaf is canonically equivalent to the
corresponding slice category. This lightweight leaf is independent of the fibred-category
packaging in `RepresentablePresheaf.Elements.Fibered`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

namespace RepresentablePresheaf.Elements

/-- Example 4.38.7 (Stacks 0044): the opposite category of elements of the representable
presheaf `h[X]` is canonically equivalent to the slice category `Over X`. -/
@[stacks 0044 "elements of a representable presheaf"]
noncomputable def overEquivalence (X : C) :
    h[X].Elementsᵒᵖ ≌ Over X :=
  (costructuredArrowYonedaEquivalence h[X]).trans
    (CostructuredArrow.overEquivalence.ofFullyFaithful yoneda X)

namespace overEquivalence

/-- The representable-elements equivalence sends the element represented by `f : U ⟶ X` to the
slice object `Over.mk f`. -/
@[simp]
theorem functor.obj
    {X U : C} (f : U ⟶ X) :
    (overEquivalence X).functor.obj
        (op (h[X].elementsMk (op U) f)) =
      Over.mk f := sorry

/-- The inverse representable-elements equivalence sends a slice arrow `f : U ⟶ X` to the
corresponding object of the opposite category of elements. -/
@[simp]
theorem inverse.obj
    {X U : C} (f : U ⟶ X) :
    (overEquivalence X).inverse.obj (Over.mk f) =
      op (h[X].elementsMk (op U) f) := sorry

/-- The representable category-of-elements equivalence strictly commutes with projection to
`C`. -/
theorem functor.comm (X : C) :
    (overEquivalence X).functor ⋙ Over.forget X =
      (π h[X]).leftOp := sorry

/-- The inverse representable category-of-elements equivalence strictly commutes with projection
to `C`. -/
theorem inverse.comm (X : C) :
    (overEquivalence X).inverse ⋙ (π h[X]).leftOp =
      Over.forget X := sorry

/-- The underlying object of the slice selected from a representable element is the domain of
that element. -/
@[simp]
theorem functor.obj.left (X : C) (a : h[X].Elementsᵒᵖ) :
    ((overEquivalence X).functor.obj a).left = (unop a).fst.unop := sorry

/-- The structure arrow of the selected slice object is the represented element, after the
canonical endpoint identification. -/
@[simp]
theorem functor.obj.hom (X : C) (a : h[X].Elementsᵒᵖ) :
    ((overEquivalence X).functor.obj a).hom =
      eqToHom (functor.obj.left X a) ≫ (unop a).snd := sorry

/-- On morphisms, the representable-elements equivalence retains the underlying arrow in `C`
as the left component of the corresponding slice morphism. -/
@[simp]
theorem functor.map.left {X : C} {a b : h[X].Elementsᵒᵖ} (φ : a ⟶ b) :
    ((overEquivalence X).functor.map φ).left =
      eqToHom (functor.obj.left X a) ≫ φ.unop.val.unop ≫
        eqToHom (functor.obj.left X b).symm := sorry

/-- The object underlying the inverse image of a slice object is its source object. -/
@[simp]
theorem inverse.obj.left (X : C) (a : Over X) :
    (unop ((overEquivalence X).inverse.obj a)).fst.unop = a.left := sorry

/-- The element selected by the inverse representable-elements equivalence is the structure
arrow of the slice object, after the canonical endpoint identification. -/
@[simp]
theorem inverse.obj.snd (X : C) (a : Over X) :
    (unop ((overEquivalence X).inverse.obj a)).snd =
      eqToHom (inverse.obj.left X a) ≫ a.hom := sorry

/-- The inverse representable-elements equivalence retains the left component of a slice
morphism as the underlying arrow in the opposite category of elements. -/
@[simp]
theorem inverse.map.left {X : C} {a b : Over X} (φ : a ⟶ b) :
    ((overEquivalence X).inverse.map φ).unop.val.unop =
      eqToHom (inverse.obj.left X a) ≫ φ.left ≫
        eqToHom (inverse.obj.left X b).symm := sorry

end overEquivalence
end RepresentablePresheaf.Elements
end CategoryTheory
