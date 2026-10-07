module

public import ReasLib.Algebra.Amitsur.Acyclic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.3.6: if `R → A` is faithfully flat, then the extended Amitsur cochain
complex with coefficients in any `R`-module `M` is acyclic. -/
@[stacks 023M] #check (@Algebra.Amitsur.extended.acyclicOfFaithfullyFlat :
  ∀ (R A M : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M],
    (Algebra.Amitsur.extended R A M).Acyclic)
