/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.PowerSeries.Inverse
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.UniformizerRoot
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weak solutions for a power-series uniformizer root

For a perfect field `k` of characteristic `p`, this leaf relates weak and formal-smooth solutions
for `k[[X]] ⊂ k[[X]][X^(1/p)]` to separability over `k((X))`.

@stack 09EP
-/

noncomputable section

-- Local instance justification (instance diamond): install the chosen fraction-field lift and
-- its scalar tower together only in this power-series specialization.
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace DVR.UniformizerRoot.PowerSeries

universe u v

variable (k : Type u) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]

local notation "A" => _root_.PowerSeries k
local notation "K" => FractionRing (_root_.PowerSeries k)
local notation "π" => (_root_.PowerSeries.X : _root_.PowerSeries k)
local notation "B" => RootRing (_root_.PowerSeries.X : _root_.PowerSeries k) p
local notation "L" => FractionRing (RootRing (_root_.PowerSeries.X : _root_.PowerSeries k) p)

variable (K₁ : Type v) [Field K₁] [Algebra (_root_.PowerSeries k) K₁]
variable [Algebra (FractionRing (_root_.PowerSeries k)) K₁]
variable [IsScalarTower (_root_.PowerSeries k) (FractionRing (_root_.PowerSeries k)) K₁]
variable [FiniteDimensional (FractionRing (_root_.PowerSeries k)) K₁]

/-- Example 15.116.2 (1): every weak solution of
`k[[X]] ⊂ k[[X]][X^(1/p)]` is inseparable over `k((X))`. -/
@[stacks 09EP "weak power-series solutions are inseparable"]
theorem not_isSeparable_of_isWeakSolutionFor :
    let _ : Fact (Irreducible π) := ⟨_root_.PowerSeries.X_irreducible⟩
    let _ : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    IsWeakSolutionFor A B K L K₁ → ¬ Algebra.IsSeparable K K₁ := sorry
-- Proof strategy: assume separability, use the uniformizer-root normalization API to produce a
-- maximal reduced-tensor-product branch whose ramification index is divisible by `p`, and
-- contradict `IsWeakSolutionFor.iff_map_maximalIdeal` on that branch.

/-- Example 15.116.2 (2): every finite inseparable extension of `k((X))` is a solution for
`k[[X]] ⊂ k[[X]][X^(1/p)]`. -/
@[stacks 09EP "finite inseparable extensions are power-series solutions"]
theorem isSolutionFor_of_not_isSeparable :
    let _ : Fact (Irreducible π) := ⟨_root_.PowerSeries.X_irreducible⟩
    let _ : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    (¬ Algebra.IsSeparable K K₁) → IsSolutionFor A B K L K₁ := sorry
-- Proof strategy: apply the reducedness criterion for tensoring with the one-`p`th-root
-- extension to obtain `y : K₁` with `y ^ p = algebraMap K K₁ π`; identify the reduced tensor
-- product and its normalization with `K₁`, then transport formal smoothness of the identity map
-- to every localized branch and conclude with `IsSolutionFor.iff_forall_ideals`.

end DVR.UniformizerRoot.PowerSeries
