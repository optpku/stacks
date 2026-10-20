/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.InjectiveHomotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

namespace FilteredInjective

/- Exercise 111.30.12: in an abelian category `𝒜`, any cochain map from a bounded-below
filtered-acyclic complex of `Filᶠ(𝒜)` to a bounded-below complex of filtered injectives is
homotopic to zero. The canonical theorem also allows unbounded source complexes, as
established in the pinned `derived.tex`, lemma-filtered-acyclic-is-zero (Stacks 05TX). -/
@[stacks 028J] #check
  (CategoryTheory.FilteredObject.FiniteDerived.FilteredInjective.nullHomotopy :
    ∀ {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (I : CochainComplex.FilteredInjectivePlus C)
    (α : K ⟶ (CochainComplex.FilteredInjectivePlus.ι C).obj I),
    FilteredObject.Finite.Homotopy.acyclic C
      ((CategoryTheory.FilteredObject.FiniteDerived.Homotopy.quotient C).obj K) →
    Nonempty (Homotopy α 0))

end FilteredInjective

end CategoryTheory.FilteredObject.FiniteDerived
