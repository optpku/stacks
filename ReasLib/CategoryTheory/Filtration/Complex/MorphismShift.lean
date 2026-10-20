/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Definition
public import ReasLib.CategoryTheory.Filtration.MorphismShift

/-!
# Filtration-Shifting Differentials of Filtered Complexes

This module owns the property that the differential of a filtered cochain complex shifts the
filtration by a prescribed integer.  The first-page construction is one consumer of the
special case of a shift by one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace FilteredComplex

namespace Differential

/-- The differential of `K` raises the filtration by `r` when every component
`K.d n (n + 1)` does so. -/
@[stacks 012N "filtration-shifting differential"]
def RaisesFiltrationBy (K : FilteredComplex C) (r : ℤ) : Prop :=
  ∀ n : ℤ, (K.d n (n + 1)).RaisesFiltrationBy r

end Differential

/-- The differential of `K` raises the filtration when it has filtration degree one. -/
@[stacks 012N "a differential which raises the filtration"]
abbrev RaisesFiltration (K : FilteredComplex C) : Prop :=
  Differential.RaisesFiltrationBy K 1

end FilteredComplex

end CategoryTheory
