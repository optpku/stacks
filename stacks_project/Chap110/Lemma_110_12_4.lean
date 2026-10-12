/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.PowerSeries.Nonflat
import StacksCheckRecall

public section

universe u

/- Lemma 110.12.4: there exists a commutative ring `R` such that the `(X)`-adic
completion `PowerSeries R` of `Polynomial R` is not flat over `R`, and a fortiori
not flat over `Polynomial R`. -/
@[stacks 0ALC] #check (PowerSeries.exists_notFlat :
    ∃ (R : Type u) (_ : CommRing R),
      ¬ Module.Flat R (PowerSeries R) ∧
        ¬ Module.Flat (Polynomial R) (PowerSeries R))
