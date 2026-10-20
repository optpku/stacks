/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Weakly.FiniteGeneration
import StacksCheckRecall

/-!
# Lemma 87.7.3

A complete linearly topologized ring with a finitely generated weakly adic
ideal is adic and has a finitely generated ideal of definition.
-/

@[expose] public section

universe u

open TopologicalRing

namespace TopologicalRing.Ideal.IsWeaklyAdic

variable {A : Type u} [CommRing A] [TopologicalSpace A]
variable [IsTopologicalRing A] [IsLinearTopology A A] [T2Space A]
variable [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]

/- Lemma 87.7.3 (1): Let `A` be a complete linearly topologized ring. Let `I`
be a finitely generated ideal such that the closure of `I ^ n` is open for all
`n ≥ 0` and these closures form a fundamental system of open ideals. Then `A`
is adic. -/
@[stacks 0GXG] #check (TopologicalRing.Ideal.IsWeaklyAdic.isAdicRing :
    ∀ {I : Ideal A}, I.FG → TopologicalRing.Ideal.IsWeaklyAdic I →
      TopologicalRing.IsAdicRing A)

/- Lemma 87.7.3 (2): Let `A` be a complete linearly topologized ring. Let `I`
be a finitely generated ideal such that the closure of `I ^ n` is open for all
`n ≥ 0` and these closures form a fundamental system of open ideals. Then `A`
has a finitely generated ideal of definition. -/
@[stacks 0GXG] #check (TopologicalRing.Ideal.IsWeaklyAdic.exists_fg_isIdealOfDefinition :
    ∀ {I : Ideal A}, I.FG → TopologicalRing.Ideal.IsWeaklyAdic I →
      ∃ J : Ideal A, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J)

end TopologicalRing.Ideal.IsWeaklyAdic
