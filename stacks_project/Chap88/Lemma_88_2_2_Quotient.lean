module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»

/-!
# Quotient stability of topologically finite type algebras

Over a Noetherian base, `C'` is stable under quotients by arbitrary ideals.
-/

@[expose] public section

noncomputable section

universe u

namespace Algebra.TopologicallyFiniteType

/-- Over a Noetherian ring, a quotient of a topologically finite type algebra
remains topologically of finite type. -/
instance instQuotient {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] (J : Ideal B) :
    TopologicallyFiniteType I (B ⧸ J) :=
  sorry

end Algebra.TopologicallyFiniteType

namespace CommAlgCat.TopologicallyFiniteType

/-- The quotient of an object of `C'` by an ideal, as an object of `C'`. -/
def quotient {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : TopologicallyFiniteType.{u} A I) (J : Ideal B) :
    TopologicallyFiniteType.{u} A I :=
  of A I (B ⧸ J)

/-- The underlying algebra of `quotient` is the quotient ring `B ⧸ J`. -/
theorem quotient_obj {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : TopologicallyFiniteType.{u} A I) (J : Ideal B) :
    (quotient I B J).obj = CommAlgCat.of A (B ⧸ J) :=
  sorry

end CommAlgCat.TopologicallyFiniteType
