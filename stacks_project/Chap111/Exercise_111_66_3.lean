module

public import ReasLib.RingTheory.Spectrum.Prime.Polynomial.Infinite
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.66.3: Let `k` be a field. Then `Spec (k[X])` has infinitely many points. -/
@[stacks 0H8S] #check (PrimeSpectrum.instInfinite_polynomial :
  ∀ {k : Type u} [Field k], Infinite (PrimeSpectrum (Polynomial k)))
