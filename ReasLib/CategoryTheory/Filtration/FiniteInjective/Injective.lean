module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.IntervalSplit.Injective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective Views of Finite Filtered-Injective Objects

Finite filtered-injectivity is defined by injectivity of the associated graded pieces.  Finiteness
then promotes this condition to injectivity of every filtration stage and of the underlying
object.  These facts are registered canonically so constructions on complexes can package their
stage and underlying views without rebuilding local instances.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C] [Abelian C]

/-- Every stage of a finite filtered-injective object is injective. -/
@[stacks 05TP "injective stages of a finite filtered-injective object"]
theorem stageInjective (I : FilteredObject.Finite.category C)
    [FilteredObject.IsFilteredInjective I.obj] (p : ℤ) :
    Injective (I.obj.stage p) := sorry

/-- The underlying object of a finite filtered-injective object is injective. -/
@[stacks 05TP "injective underlying object of a finite filtered-injective object"]
theorem underlyingInjective (I : FilteredObject.Finite.category C)
    [FilteredObject.IsFilteredInjective I.obj] :
    Injective I.obj.obj := sorry

attribute [instance] stageInjective underlyingInjective

end CategoryTheory.FilteredObject.Finite.FilteredInjective
