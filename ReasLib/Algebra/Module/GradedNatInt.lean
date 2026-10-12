/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.GradedModule
public import ReasLib.Algebra.Group.Action.NatInt

/-!
# Natural degrees acting on integer degrees

A nonnegative graded ring acts on an integer-graded module by translation of degrees.  This file
is the graded-module integration facade; the grading-independent action itself is owned by
`AddAction.natInt` in `ReasLib.Algebra.Group.Action.NatInt`.
-/

@[expose] public section

/-
API design: this facade intentionally declares no parallel instance.  Importing it combines
Mathlib's graded-module API with the lower action owner, while direct-sum and non-graded users can
public import the lower leaf without paying for the graded-module dependency.
-/

