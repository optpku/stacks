/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Extension.HeightOne
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.124.4 (0ASI)

The height-one branch condition and the power-descent theorem are owned by ReasLib. This chapter
file records the source statement without rebuilding the divisor-ideal proof infrastructure.

@stack 0ASI
-/

/- Lemma 15.124.4 (0ASI): an `n`-th power up to a unit descends along the stated flat local map. -/
@[stacks 0ASI "Lemma 15.124.4: descent of an n-th power up to a unit"]
#check @HeightOneLocalization.exists_unit_mul_pow_of_map_eq_unit_mul_pow

#check @HeightOneLocalization.IsWeaklyUnramifiedBranch
#check @HeightOneLocalization.HasWeaklyUnramifiedBranches
#check @HeightOneLocalization.HasWeaklyUnramifiedBranches.existsBranch

end
