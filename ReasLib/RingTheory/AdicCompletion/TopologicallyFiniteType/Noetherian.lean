module

public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Topologically finite type algebras over Noetherian rings

Over a Noetherian base, topologically finite type algebras are Noetherian and
closed under ideal quotients. Adic completions of finite type algebras are
topologically of finite type.
-/

@[expose] public section

universe u

namespace Algebra.TopologicallyFiniteType

/-- Over a Noetherian ring, every topologically finite type algebra is Noetherian. -/
theorem isNoetherianRing {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] :
    IsNoetherianRing B :=
  sorry

/-- The adic completion of a finite type algebra over a Noetherian ring is
topologically of finite type with respect to the defining ideal. -/
instance instOfFiniteType {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    TopologicallyFiniteType I (AdicCompletion (I.map (algebraMap A C)) C) :=
  sorry

/-- Over a Noetherian ring, a quotient of a topologically finite type algebra
remains topologically of finite type. -/
instance instQuotient {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] (J : Ideal B) :
    TopologicallyFiniteType I (B ⧸ J) :=
  sorry

end Algebra.TopologicallyFiniteType
