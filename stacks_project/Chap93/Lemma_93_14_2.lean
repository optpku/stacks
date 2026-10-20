module

public import ReasLib.RingTheory.Henselian.Pair.Exal
import StacksCheckRecall

universe u

/- Lemma 93.14.2
For a finite type algebra over a field, smooth away from V(J), henselization
induces a canonical bijection on first-order extensions with finite coefficients.
-/
@[stacks 0DZC] #check (Algebra.Exal.henselization_bijective :
  ∀ (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N] [Algebra.FiniteType k B] [Module.Finite B N]
    (J : Ideal B),
    (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ⊆ Algebra.smoothLocus k B →
      Function.Bijective (Algebra.Exal.henselization k B N J))
