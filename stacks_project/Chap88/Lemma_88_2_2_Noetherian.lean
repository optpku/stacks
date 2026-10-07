module

public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»

/-!
# Noetherianity of topologically finite type algebras

Over a Noetherian base ring, every algebra in `C'` is Noetherian.
This cannot be a global instance: `IsNoetherianRing B` does not determine the
ideal `I` or the base algebra, matching `Algebra.FiniteType.isNoetherianRing`.
-/

@[expose] public section

universe u

namespace Algebra.TopologicallyFiniteType

/-- Over a Noetherian ring, every topologically finite type algebra is Noetherian. -/
theorem instIsNoetherianRing {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] :
    IsNoetherianRing B :=
  sorry

end Algebra.TopologicallyFiniteType
