/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Weakly
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 87.7.1 (1): a linearly topologized ring is weakly pre-adic if there
exists an ideal `I` such that the closure of `I ^ n` is open for all `n ≥ 0` and
these closures form a fundamental system of open ideals. -/
@[stacks 0GXE] #check
  (@TopologicalRing.IsWeaklyPreadicRing :
    ∀ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R), Prop)

/- Definition 87.7.1 (2): a linearly topologized ring is weakly adic if it is
weakly pre-adic and complete, including separated. -/
@[stacks 0GXE] #check
  (@TopologicalRing.IsWeaklyAdicRing :
    ∀ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R), Prop)
