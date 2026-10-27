/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Etale
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange
public import stacks_project.Chap77.Lemma_77_12_3_Comparison

/-! # Compatibility of pushed formal-system stage transitions -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem

/-- The transition from a pushed successor stage module to the preceding stage module. -/
abbrev pushedStageSuccessor (S : ProperFlatFormalSystem) (n : ℕ) :=
  pushforwardStep S n

#check (pushedStageSuccessor : ∀ (S : ProperFlatFormalSystem) (n : ℕ),
  S.pushforwardModule (n + 1) ⟶ S.pushforwardModule n)

end AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem
