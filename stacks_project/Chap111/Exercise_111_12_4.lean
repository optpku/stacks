module

public import ReasLib.RingTheory.MvPowerSeries.DepthDim
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.12.4 (1): for a field `k` and naturals `n ≤ m`, the Noetherian
local ring `Ring k m n` satisfies `ringKrullDim (Ring k m n) = m`. -/
@[stacks 0CS4] #check
  (MvPowerSeries.DepthDim.ringKrullDim_eq :
    ∀ (k : Type u) [Field k] (m n : ℕ), n ≤ m →
      ringKrullDim (MvPowerSeries.DepthDim.Ring k m n) = m)

/- Exercise 111.12.4 (2): for a field `k` and naturals `n ≤ m`, the Noetherian
local ring `Ring k m n` satisfies `moduleDepth (Ring k m n) (Ring k m n) = n`. -/
@[stacks 0CS4] #check
  (MvPowerSeries.DepthDim.moduleDepth_eq :
    ∀ (k : Type u) [Field k] (m n : ℕ), n ≤ m →
      moduleDepth (MvPowerSeries.DepthDim.Ring k m n)
        (MvPowerSeries.DepthDim.Ring k m n) = n)
