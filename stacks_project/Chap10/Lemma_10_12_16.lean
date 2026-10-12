/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.TensorProduct
import StacksCheckRecall

/-!
# Lemma 10.12.16
@stack 00DL
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.12.16 (Stacks tag `00DL`) is a bridge/view recall.  The reusable owner is
`LocalizedModule.tensorProductLinearEquiv`; its pure-tensor formula is exposed by the companion
`LocalizedModule.tensorProductLinearEquiv_apply_mk_tmul_mk`.  Consumers should import the ReasLib
leaf directly rather than depend on this chapter-facing file. -/
@[stacks 00DL "(1)"]
#check @LocalizedModule.tensorProductLinearEquiv
@[stacks 00DL "(2)"]
#check @LocalizedModule.tensorProductLinearEquiv_apply_mk_tmul_mk
