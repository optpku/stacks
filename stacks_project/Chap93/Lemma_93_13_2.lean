module

public import ReasLib.RingTheory.Extension.SquareZero.Localization
import StacksCheckRecall

universe u

/- Lemma 93.13.2
For a finite type algebra over a field and a finite coefficient module, localization at a
multiplicative subset disjoint from every nonsmooth prime induces a canonical bijection
on first-order square-zero extension classes.
-/
@[stacks 0DZ8] #check (Algebra.Exal.localize_bijective :
  ∀ (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N] [Algebra.FiniteType k B] [Module.Finite B N]
    (S : Submonoid B),
    (∀ q : PrimeSpectrum B, q ∉ Algebra.smoothLocus k B →
      (S : Set B) ∩ q.asIdeal = ∅) →
    Function.Bijective (Algebra.Exal.localize k B N S))
