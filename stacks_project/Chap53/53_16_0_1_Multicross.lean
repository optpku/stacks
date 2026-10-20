module

public import ReasLib.RingTheory.PowerSeries.Multicross

universe u

#check (Multicross.ring :
  (k : Type u) → [Field k] → (n : ℕ) → Subring (Fin n → PowerSeries k))
