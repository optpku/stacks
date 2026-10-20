module

public import ReasLib.RingTheory.AdicAlgebraSystem

@[expose] public section

universe u

#check (AdicAlgebraSystem.{u} : ∀ (A : Type u) [CommRing A], Ideal A → Type (u + 1))
