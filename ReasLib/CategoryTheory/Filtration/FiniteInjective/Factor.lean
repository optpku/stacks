module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.Strict
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension across Strict Monomorphisms

Maps to finite filtered-injective objects extend across strict monomorphisms. This is the
filtered analogue of `Injective.factors`, with the finite filtration retained as part of the
source mathematics.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C] [Abelian C]

/-- Lemma 13.26.4 (`05TR`): a map to a finite filtered-injective object extends across a strict
monomorphism. -/
@[stacks 05TR]
theorem factors {A B : FilteredObject C} {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj] (f : A ⟶ I.obj) (u : A ⟶ B)
    [Mono u.hom] (hu : FilteredObject.Hom.Strict u) :
    ∃ g : B ⟶ I.obj, u ≫ g = f := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective
