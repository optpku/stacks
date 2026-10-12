/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DirectLimit
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.8.3: for a directed system of modules, the colimit is canonically the quotient of the
disjoint union by eventual equality; addition, scalar multiplication, and the canonical stage maps
are inherited from the system.  The generic quotient carrier and its comparison with the
categorical colimit are owned by ReasLib/Mathlib.

@stack 00D6
-/

@[stacks 00D6 "direct-limit eventual equality"]
#check @DirectLimit.Module.of_eq_iff

@[stacks 00D6 "direct-limit quotient comparison"]
#check @Module.DirectLimit.linearEquiv

@[stacks 00D6 "direct-limit addition"]
#check @DirectLimit.add_def

@[stacks 00D6 "direct-limit scalar multiplication"]
#check @DirectLimit.smul_def

@[stacks 00D6 "direct-limit canonical stage map"]
#check @DirectLimit.Module.of

@[stacks 00D6 "direct-limit colimit comparison"]
#check @ModuleCat.directLimitColimitIso

@[stacks 00D6 "direct-limit colimit comparison leg"]
#check @ModuleCat.directLimitColimitIso_ι
