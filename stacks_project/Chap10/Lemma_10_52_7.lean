/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Length.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Length after localization

@stack 00IZ

Lemma 10.52.7 is the canonical localization-length inequality owned by ReasLib.
-/

@[stacks 00IZ]
#check @length_localizedModule_le
