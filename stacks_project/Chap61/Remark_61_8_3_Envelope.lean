module

public import ReasLib.Algebra.IndEtaleEnvelope.Envelope

@[expose] public section

universe u

/-! The ind-étale envelope is provided by the reusable algebraic construction. -/

#check (Algebra.IndEtaleEnvelope : ∀ (A : Type u) [CommRing A], Type u)
