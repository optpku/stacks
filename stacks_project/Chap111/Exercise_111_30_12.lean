module

public import ReasLib.CategoryTheory.Filtration.Derived.InjectiveHomotopy
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory HomologicalComplex
open FilteredObject.Finite.Homotopy

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

namespace FilteredInjective

/-- Exercise 111.30.12: in an abelian category `𝒜`, any cochain map from a bounded-below
filtered-acyclic complex of `Filᶠ(𝒜)` to a bounded-below complex of filtered injectives is
homotopic to zero. -/
@[stacks 028J]
theorem homotopicToZero {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK_plus : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (I : CochainComplex.FilteredInjectivePlus C)
    (α : K ⟶ (CochainComplex.FilteredInjectivePlus.ι C).obj I)
    (hK_acyclic : acyclic C ((Homotopy.quotient C).obj K)) :
    Nonempty (Homotopy α 0) := sorry

end FilteredInjective

end CategoryTheory.FilteredObject.FiniteDerived
