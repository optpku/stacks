/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Exact
import StacksCheckRecall

/-!
# Exactness properties of formal gluing

@stack 05EN
-/

@[expose] public section

/- Lemma 15.90.13 (1): formal gluing along a flat ring map is abelian. -/
@[stacks 05EN "(1) formal gluing is abelian"]
#check @LocalizedModule.Away.FormalGluing.existsAbelian_of_flat

/- Lemma 15.90.13 (2): canonical formal gluing along a flat ring map is exact. -/
@[stacks 05EN "(2) exactness of canonical formal gluing"]
#check @LocalizedModule.Away.FormalGluing.existsExactOfModule_of_flat

/- Lemma 15.90.13 (3): canonical formal gluing along a flat ring map preserves colimits. -/
@[stacks 05EN "(3) canonical formal gluing preserves colimits"]
#check @LocalizedModule.Away.FormalGluing.ofModule_preservesColimits_of_flat
