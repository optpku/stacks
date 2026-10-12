/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Characterizations of Triangulated Object Properties

Mathlib owns `ObjectProperty.IsTriangulated` and its primitive closure fields.
This leaf adds the bridge through the Verdier morphism property `trW`.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C)

/-- Lemma 13.4.16 (3): every morphism between objects of a triangulated object property belongs
to its Verdier morphism property. -/
@[stacks 05QX]
theorem trW_of_isTriangulated
    (hTriangulated : P.IsTriangulated)
    {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.trW f := sorry

/-- Lemma 13.4.16 (4): an object property is triangulated when it contains zero, is stable under
shifts, and its morphisms between members belong to its Verdier morphism property. -/
@[stacks 05QX]
theorem isTriangulated_of_containsZero_of_isStableUnderShift_of_trW
    (hZero : P.ContainsZero) (hShift : P.IsStableUnderShift ℤ)
    (hW : ∀ {X Y : C} (f : X ⟶ Y) (_ : P X) (_ : P Y), P.trW f) :
    P.IsTriangulated := sorry

end CategoryTheory.ObjectProperty
