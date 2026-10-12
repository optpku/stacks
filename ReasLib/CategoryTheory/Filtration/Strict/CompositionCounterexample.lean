/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Abelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Failure of Closure of Strict Morphisms under Composition

Strict filtered morphisms are not closed under composition without an additional hypothesis.
Positive closure results, for a monomorphic second map or an epimorphic first map, are provided
by `ReasLib.CategoryTheory.Filtration.Strict.Composition`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredObject.Hom

/-- In general, the composite of strict morphisms of filtered objects need not be strict. -/
@[stacks 05SJ]
theorem strict_comp_not_in_general :
    ¬ ∀ {C : Type u} [Category.{v} C] [Abelian C] {A B D : FilteredObject C}
        (f : A ⟶ B) (g : B ⟶ D), Strict f → Strict g → Strict (f ≫ g) := sorry

end CategoryTheory.FilteredObject.Hom
