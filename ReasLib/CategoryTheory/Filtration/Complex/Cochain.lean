module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered Cochain Complexes

@stack 012L

Source-facing cochain-complex vocabulary for the general `FilteredComplex` construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

noncomputable section

/-- Definition 12.24.1 [012L] compatibility vocabulary: a source-facing synonym for a filtered
cochain complex, implemented by the canonical owner `FilteredComplex`. -/
@[stacks 012L "filtered cochain-complex vocabulary"]
abbrev FilteredCochainComplex (C : Type u) [Category.{v} C] [HasZeroMorphisms C] :=
  FilteredComplex C

end

end CategoryTheory
