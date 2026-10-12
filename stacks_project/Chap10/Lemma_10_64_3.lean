/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.SymbolicPower
import StacksCheckRecall

/-!
# Flat base change of symbolic powers

@stack 0BC0
-/

@[expose] public section

/- Lemma 10.64.3: under a flat ring map, symbolic powers commute with extension
when the extended prime remains prime. -/
@[stacks 0BC0]
#check @Ideal.map_symbolicPower_eq_symbolicPower_map
