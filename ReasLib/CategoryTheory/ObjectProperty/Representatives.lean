/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sets of representatives for essentially small object properties

This file turns Mathlib's categorical `ObjectProperty.EssentiallySmall` API into the equivalent
existence of a set containing exactly one representative of every isomorphism class satisfying
the property.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- An essentially small,
isomorphism-closed property admits a set containing exactly one representative of each
isomorphism class. -/
@[stacks 040B "object-property form"]
theorem EssentiallySmall.exists_set_representatives
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ S : Set C,
      (∀ X ∈ S, P X) ∧
      ∀ X : C, P X → ∃! Y : C, Y ∈ S ∧ Nonempty (Y ≅ X) := sorry

end CategoryTheory.ObjectProperty
