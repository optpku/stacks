/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.QuasiSeparated
public import stacks_project.Chap87.Remark_87_13_4_Ideals_of_definition_System

/-!
# Remark 87.18.2

Every quasi-compact and quasi-separated EGA formal scheme has a fundamental
system of ideals of definition.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- Remark 87.18.2: every quasi-compact and quasi-separated formal scheme has a
fundamental system of ideals of definition. This is the translation of
Lemma 87.18.1 into the language of EGA formal schemes, using Remark 87.13.4. -/
@[stacks 0AJF]
theorem exists_fundamentalSystem (X : FormalScheme.{u})
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] :
    Nonempty (FundamentalSystem X) := sorry

end AlgebraicGeometry.FormalScheme
