/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPowerSeries.HigherTorIntersection
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

/- Example 43.14.4 (1): the scheme-theoretic intersection of the union of the two
coordinate planes with the diagonal plane has length three. -/
@[stacks 0B2S] #check
  (MvPowerSeries.HigherTorIntersection.quotientLength_eq_three :
    Module.length MvPowerSeries.HigherTorIntersection.PowerSeriesRing
      (MvPowerSeries.HigherTorIntersection.PowerSeriesRing ⧸
        (MvPowerSeries.HigherTorIntersection.reduciblePlaneIdeal ⊔
          MvPowerSeries.HigherTorIntersection.diagonalPlaneIdeal)) = 3)

/- Example 43.14.4 (2): the local intersection multiplicity, computed using all higher
`Tor` modules, is two rather than the length-three degree-zero contribution. -/
@[stacks 0B2S] #check
  (MvPowerSeries.HigherTorIntersection.torEulerCharacteristic_eq_two :
    ∑ᶠ i : ℕ, (Int.negOnePow i : ℤ) *
      ((Module.length MvPowerSeries.HigherTorIntersection.PowerSeriesRing
        (CategoryTheory.ModuleCat.Tor.obj i
          (ModuleCat.of
            MvPowerSeries.HigherTorIntersection.PowerSeriesRing
            (MvPowerSeries.HigherTorIntersection.PowerSeriesRing ⧸
              MvPowerSeries.HigherTorIntersection.reduciblePlaneIdeal))
          (ModuleCat.of
            MvPowerSeries.HigherTorIntersection.PowerSeriesRing
            (MvPowerSeries.HigherTorIntersection.PowerSeriesRing ⧸
              MvPowerSeries.HigherTorIntersection.diagonalPlaneIdeal)))).toNat : ℤ) =
      2)
