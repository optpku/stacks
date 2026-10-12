/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.JacobiZariski
import StacksCheckRecall

/-!
# Lemma 10.138.9

@stack 031K
-/

@[expose] public section

/- Lemma 10.138.9 [stacks 031K]: canonical recall of the reusable split
Jacobi-Zariski transitivity theorem for formally smooth algebra maps. -/

@[stacks 031K]
#check @KaehlerDifferential.transitivity_sequence_splits_of_formallySmooth
