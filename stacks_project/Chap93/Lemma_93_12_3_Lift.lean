module

public import ReasLib.RingTheory.Algebra.FlatLift.AdicCompletion

/-!
# Flat algebra lift and syntomic complement predicates
-/

@[expose] public section

universe u v

#check (Algebra.NilpotentLift.existsFlatLift :
  ∀ (A' : Type u) [CommRing A'] (A : Type u) [CommRing A] [Algebra A' A]
    (B : Type u) [CommRing B] [Algebra A B], Prop)

#check (RingHom.SyntomicOnComplement :
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S],
    (R →+* S) → Ideal S → Prop)

end
