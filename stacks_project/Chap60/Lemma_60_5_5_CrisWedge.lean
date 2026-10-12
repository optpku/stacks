/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_5_4

@[expose] public section

/-- Completed crystalline objects of `Cris^∧(C/A)` are the Remark 60.5.4 owner. -/
abbrev DividedPowerThickening.CrisWedgeObject :=
  CompletedCrisObject
