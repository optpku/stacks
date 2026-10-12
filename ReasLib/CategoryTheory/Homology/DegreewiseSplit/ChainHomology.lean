/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.ChainShiftSequence
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.Chain
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology Boundary of a Degreewise Split Chain Short Complex

The explicit chain connecting morphism associated to a degreewise splitting induces the
canonical boundary in the long exact homology sequence.
-/

@[expose] public section

open ComplexShape HomologicalComplex

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DegreewiseSplit.Chain

/-- The shifted homology map of the chain connecting morphism associated to a degreewise
splitting is the canonical boundary of the short exact sequence. -/
@[stacks 011E]
theorem boundary_eq_δ
    {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact)
    (σ : ∀ n : ℤ, (S.degreewise n).Splitting) (i : ℤ) :
    (HomologicalComplex.homologyFunctor C (down ℤ) 0).shiftMap
        (ChainComplex.homOfDegreewiseSplit S σ) i (i - 1) (neg_add_eq_sub 1 i) =
      hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) := sorry

end DegreewiseSplit.Chain

end

end CategoryTheory.ShortComplex.ShortExact
