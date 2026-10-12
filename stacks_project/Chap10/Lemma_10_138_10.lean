/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.JacobiZariski
import StacksCheckRecall

/-!
# Lemma 10.138.10

@stack 06A6
-/

@[expose] public section

/- Lemma 10.138.10 [stacks 06A6]: canonical recall of the section of the
Kähler base-change map supplied by formal smoothness and a surjective target
map. -/

@[stacks 06A6]
#check @KaehlerDifferential.mapBaseChange_has_section_of_formallySmooth
