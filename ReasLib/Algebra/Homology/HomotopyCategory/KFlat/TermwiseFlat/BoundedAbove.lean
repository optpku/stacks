/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.BoundedAbove
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above K-flat termwise-flat homotopy objects

This leaf lifts the bounded-above criterion for cochain complexes to the canonical object
property of good models in the homotopy category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [HasCountableCoproducts C] [CountableAB4 C]

/-- A homotopy object represented by a bounded-above complex with flat terms belongs to the
canonical full subcategory of K-flat termwise-flat models. -/
@[stacks 06YQ "bounded-above good models"]
theorem of_boundedAbove {K : HomotopyCategory C (ComplexShape.up ℤ)}
    (hFlat : HomologicalComplex.IsTermwiseFlat K.as)
    (hbounded : CochainComplex.minus C K.as) :
    HomotopyCategory.KFlat.termwiseFlat C K := sorry

end CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat
