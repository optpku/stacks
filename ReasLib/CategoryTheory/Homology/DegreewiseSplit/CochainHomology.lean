/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology Boundary of a Degreewise Split Cochain Short Complex

The cochain connecting morphism associated to a degreewise splitting induces the canonical
boundary in the long exact cohomology sequence.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DegreewiseSplit.Cochain

/-- The cohomology boundary of the triangle associated to a degreewise splitting is the
canonical boundary of the short exact sequence. -/
@[stacks 011K]
theorem boundary_eq_δ
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (σ : ∀ n : ℤ, (S.degreewise n).Splitting) (i : ℤ) :
    CochainComplex.homologyδOfTriangle
        (CochainComplex.triangleOfDegreewiseSplit S σ) i (i + 1) rfl =
      hS.δ i (i + 1) rfl := sorry

end DegreewiseSplit.Cochain

end

end CategoryTheory.ShortComplex.ShortExact
