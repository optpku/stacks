/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology-Acyclic Homotopy Objects

This module provides the homology-vanishing object property for cochain homotopy categories
under the minimal `CategoryWithHomology` assumptions.  Mathlib's
`HomotopyCategory.subcategoryAcyclic` remains the abelian specialization with its additional
triangulated structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.HomotopyCategory.Homology

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/-- A cochain homotopy object is acyclic when every one of its homology objects is zero. -/
@[stacks 05RZ "homology-acyclic homotopy object"]
def acyclic : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K ↦ ∀ n : ℤ,
    IsZero ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj K)

namespace Acyclic

/-- Membership in `HomotopyCategory.Homology.acyclic C` is precisely degreewise vanishing of
homology. -/
@[stacks 05RZ "homology-acyclic homotopy object"]
theorem iff (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    acyclic C K ↔ ∀ n : ℤ,
      IsZero ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj K) := sorry

end Acyclic

end CategoryTheory.HomotopyCategory.Homology
