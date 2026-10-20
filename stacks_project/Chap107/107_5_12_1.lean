/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.KrullDimension.MaximalChain
import StacksCheckRecall

@[expose] public section

universe u

open TopologicalSpace Order

/- 107.5.12.1: if `X` is finite-dimensional of dimension `d`, there is a maximal
strictly decreasing chain `Z₀ ⊃ Z₁ ⊃ … ⊃ Z_d` of irreducible closed subsets.
This is a `RelSeries` of `IrreducibleCloseds X` under `· > ·` of length `d`;
the hypothesis `topologicalKrullDim X = d` makes the chain longest, so the last
term is a minimal irreducible closed subset. -/
@[stacks 0DRS] #check
  (exists_gtRelSeries_length_eq_topologicalKrullDim :
    ∀ {X : Type u} [TopologicalSpace X] {d : ℕ}, topologicalKrullDim X = d →
      ∃ Z : RelSeries {(a, b) : IrreducibleCloseds X × IrreducibleCloseds X | a > b},
        Z.length = d)
