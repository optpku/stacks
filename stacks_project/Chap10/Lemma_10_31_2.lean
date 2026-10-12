/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPowerSeries.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
# Noetherian multivariate power series rings

@stack 0306

Lemma 10.31.2 is recalled through the finite-variable Noetherian owner.  The old `Fin n` proof
scaffolding was only a presentation of the same typeclass fact and is intentionally absent from
the source-facing file.
-/

/- Lemma 10.31.2: if `R` is Noetherian and `σ` is finite, then `MvPowerSeries σ R` is Noetherian. -/
@[stacks 0306 "canonical finite-variable owner"]
#check @MvPowerSeries.instIsNoetherianRing
