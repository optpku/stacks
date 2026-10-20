/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Weakly.FiniteGeneration
import StacksCheckRecall

/-!
# Lemma 87.7.4

A weakly adic topological ring with an ideal of definition `I` such that
`I / I₂` is finitely generated, where `I₂` is the closure of `I ^ 2`, is adic
and has a finitely generated ideal of definition.
-/

@[expose] public section

universe u

open TopologicalRing

namespace TopologicalRing.IsWeaklyAdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdicRing A]

/- Lemma 87.7.4 (1): Let `A` be a weakly adic topological ring. Let `I` be an
ideal of definition such that `I / I₂` is a finitely generated module, where
`I₂` is the closure of `I ^ 2`. Then `A` is adic. -/
@[stacks 0GXH] #check (TopologicalRing.IsWeaklyAdicRing.isAdicRing :
    ∀ {I : Ideal A}, Ideal.IsIdealOfDefinition I →
      Module.Finite A (I ⧸ Submodule.comap I.subtype (I ^ 2).closure) →
      IsAdicRing A)

/- Lemma 87.7.4 (2): Let `A` be a weakly adic topological ring. Let `I` be an
ideal of definition such that `I / I₂` is a finitely generated module, where
`I₂` is the closure of `I ^ 2`. Then `A` has a finitely generated ideal of
definition. -/
@[stacks 0GXH] #check (TopologicalRing.IsWeaklyAdicRing.exists_fg_isIdealOfDefinition :
    ∀ {I : Ideal A}, Ideal.IsIdealOfDefinition I →
      Module.Finite A (I ⧸ Submodule.comap I.subtype (I ^ 2).closure) →
      ∃ J : Ideal A, J.FG ∧ Ideal.IsIdealOfDefinition J)

end TopologicalRing.IsWeaklyAdicRing
