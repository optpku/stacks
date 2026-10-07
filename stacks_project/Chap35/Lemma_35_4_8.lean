module

public import ReasLib.LinearAlgebra.UniversallyInjective.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 35.4.8 (08WP): any faithfully flat ring map is universally injective. -/
@[stacks 08WP] #check
  (@Module.FaithfullyFlat.universallyInjective_algebraLinearMap :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Module.FaithfullyFlat R S],
      LinearMap.UniversallyInjective.{u, u, v, w} (Algebra.linearMap R S))
