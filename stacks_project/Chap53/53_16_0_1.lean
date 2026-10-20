module

public import ReasLib.RingTheory.PowerSeries.Multicross
import StacksCheckRecall

universe u

/- 53.16.0.1: `A` is the subring of tuples `f : Fin n → PowerSeries k` satisfying
`PowerSeries.constantCoeff (f i) = PowerSeries.constantCoeff (f j)` for all `i` and `j`. -/
@[stacks 0C1U] #check (Multicross.ring :
  (k : Type u) → [Field k] → (n : ℕ) → Subring (Fin n → PowerSeries k))
