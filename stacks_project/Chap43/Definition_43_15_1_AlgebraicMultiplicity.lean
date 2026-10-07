module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity

universe u v

#check (Ideal.HilbertSamuel.multiplicityInDegree :
  {R : Type u} → [CommRing R] → (I : Ideal R) → (M : Type v) →
    [AddCommGroup M] → [Module R M] → ℕ → ℚ)

#check (Ideal.HilbertSamuel.multiplicity :
  {R : Type u} → [CommRing R] → (I : Ideal R) → (M : Type v) →
    [AddCommGroup M] → [Module R M] → ℚ)
