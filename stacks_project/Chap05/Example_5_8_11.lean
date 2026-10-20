/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Cofinite.Basic
public import ReasLib.Topology.Indiscrete
public import ReasLib.Topology.Sum
import StacksCheckRecall

@[expose] public section

universe u v

section

variable (X : Type u) [TopologicalSpace X]
variable (Y : Type v)

/-!
# Example 5.8.11

The source's two concrete coproduct examples are specializations of ReasLib's
sum-obstruction API. The textbook assumptions remain in the tagged checks;
the general theorems stay in `ReasLib.Topology.Sum`.
-/

/- ReasLib's source-independent sum obstructions are the proof-level core. -/
#check @Sum.not_t0_of_not_t0_left
#check @Sum.not_quasiSober_of_not_quasiSober_right

/- Example 5.8.11 (1): an indiscrete nontrivial left summand makes the displayed coproduct
non-Kolmogorov. -/
@[stacks 0B34 "the coproduct is not Kolmogorov"]
#check fun [IndiscreteTopology X] [Nontrivial X] [Infinite Y] ↦
  Sum.not_t0_of_not_t0_left (X := X) (Y := CofiniteTopology Y)
    IndiscreteTopology.not_t0

/- Example 5.8.11 (2): an infinite cofinite right summand makes the displayed coproduct
non-quasi-sober. -/
@[stacks 0B34 "the coproduct is not quasi-sober"]
#check fun [IndiscreteTopology X] [Nontrivial X] [Infinite Y] ↦
  Sum.not_quasiSober_of_not_quasiSober_right (X := X) (Y := CofiniteTopology Y)
    CofiniteTopology.not_quasiSober

end
