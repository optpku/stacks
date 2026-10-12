/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.StableFree.Lift
import StacksCheckRecall

/-!
# Lifting finite stably free modules

@stack 0BC5

Lemma 15.3.3 states that finite stably free modules lift across an ideal contained in the
Jacobson radical.  The shared owner retains the source's noncommutative ring and two-sided ideal
hypotheses.
-/

@[expose] public section

/- Lemma 15.3.3: if `I ≤ Ring.jacobson R`, every finite stably free `R ⧸ I`-module is the
reduction of a finite stably free `R`-module. -/
@[stacks 0BC5 "Lemma 15.3.3"]
#check @Module.StablyFree.exists_lift_of_le_jacobson
