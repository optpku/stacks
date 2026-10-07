module

public import ReasLib.RingTheory.Frobenius.Colimit

universe u

/- The chapter compatibility surface re-exports the reusable Frobenius-colimit ring API. -/
#check (Ring.FrobeniusColimit.ring :
  ∀ (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (ZMod p) A],
    CommRingCat.{u})
