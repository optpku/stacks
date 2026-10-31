/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.InjectivePredicate
import StacksCheckRecall

universe v u

@[expose] public section

variable {C : Type u} [CategoryTheory.Category.{v} C]
  [CategoryTheory.Limits.HasZeroObject C]
  [CategoryTheory.Limits.HasZeroMorphisms C]
  [CategoryTheory.Limits.HasCokernels C]

/- Definition 111.30.3: for an abelian category `𝒜`, a finite decreasing filtration of an object
`A` is filtered injective when every successive quotient, represented by the cokernel of the
inclusion from stage `p + 1` to stage `p`, is injective in `𝒜`. -/
@[stacks 028A] #check
  (CategoryTheory.DecreasingFiltration.Finite.IsFilteredInjective :
    CategoryTheory.FilteredObject.Finite.category C → Prop)
