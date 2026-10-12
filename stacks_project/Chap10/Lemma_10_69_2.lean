/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic
import StacksCheckRecall

/-!
# Lemma 10.69.2

@stack 00LN
-/

@[expose] public section

/- Lemma 10.69.2, tag `00LN`: the owner-level regular-to-quasi implication
belongs to the shared sequence regularity hierarchy. -/
@[stacks 00LN "regular sequences are quasi-regular"]
#check @RingTheory.Sequence.IsRegular.isQuasiRegular
