module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.ParallelPairCocones
public import ReasLib.CategoryTheory.Filtered.SpanCocones

/-!
# Filtered connected components

Span cocones supply common successors inside a connected component, while parallel-pair cocones
supply the remaining filteredness axiom.  This module packages that recurring passage once.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]

namespace ConnectedComponents

namespace component

/-- Lemma 4.19.8 (Stacks 002X): every connected component is filtered when the ambient category
has span cocones and parallel-pair cocones. -/
@[stacks 002X "filtered connected components from weak cocones"]
instance isFiltered
    [HasSpanCocones I] [HasParallelPairCocones I]
    (j : ConnectedComponents I) :
    IsFiltered j.Component := sorry

/-- Lemma 4.19.8 (Stacks 002X): span cocones together with postcomposition equalizers make every
connected component filtered. -/
@[stacks 002X "connected components are filtered"]
theorem isFiltered_of_postcomposition
    [HasSpanCocones I]
    (hMap :
      ∀ ⦃X Y : I⦄ (f g : X ⟶ Y),
        ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h)
    (j : ConnectedComponents I) :
    IsFiltered j.Component := sorry

end component

end ConnectedComponents

end CategoryTheory
