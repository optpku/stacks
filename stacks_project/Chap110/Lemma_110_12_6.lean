/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Coherent.Valuation
public import ReasLib.RingTheory.Flatness.MittagLeffler.PowerSeries
import StacksCheckRecall

@[expose] public section

universe u

namespace PowerSeries

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]

/- Lemma 110.12.6 (1): if `R` is a valuation ring, then `PowerSeries R` is
flat as an `R`-module. -/
@[stacks 0F1Z] #check (inferInstance : Module.Flat R (PowerSeries R))

/-- Lemma 110.12.6 (2): if `R` is a valuation ring of Krull dimension greater
than `1`, then `PowerSeries R` is not flat as a `Polynomial R`-module. -/
@[stacks 0F1Z]
theorem not_flat_polynomial (hdim : 1 < ringKrullDim R) :
    ¬ Module.Flat (Polynomial R) (PowerSeries R) := sorry

end PowerSeries
