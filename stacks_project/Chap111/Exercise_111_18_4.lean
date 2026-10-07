module

import StacksCheckRecall
import ReasLib.RingTheory.Catenary.Field

@[expose] public section

universe u v

/- Exercise 111.18.4: Every finite type algebra over a field is catenary. -/
@[stacks 077D] #check
  (IsCatenaryRing.of_finiteType_over_field :
    ∀ (k : Type u) [Field k] (A : Type v) [CommRing A]
      [Algebra k A] [Algebra.FiniteType k A], IsCatenaryRing A)
