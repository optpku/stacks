/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Simple
import StacksCheckRecall

/-!
# Simple modules

Definition 10.52.9 recalls the canonical simple-module predicate and its submodule-lattice
characterization.

@stack 00J1
-/

@[expose] public section

/- Definition 10.52.9 (Tag 00J1): the canonical simple-module predicate and
its source-facing submodule-lattice characterization are shared through
`ReasLib.Algebra.Module.Simple`. -/
@[stacks 00J1 "simple module"]
#check @IsSimpleModule
@[stacks 00J1 "simple module lattice criterion"]
#check @isSimpleModule_iff_nontrivial_and_submodule_eq_bot_or_eq_top
