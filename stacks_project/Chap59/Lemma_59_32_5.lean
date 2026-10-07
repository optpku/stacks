module

public import ReasLib.RingTheory.Henselian.Finite
import StacksCheckRecall

universe u v

/- Lemma 59.32.5: If R is henselian and A is a finite R-algebra, then A is a
finite product of henselian local rings. -/
@[stacks 03QJ] #check
  (HenselianLocalRing.FiniteProduct.nonempty :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [HenselianLocalRing R] [Module.Finite R S],
      Nonempty (HenselianLocalRing.FiniteProduct R S))
