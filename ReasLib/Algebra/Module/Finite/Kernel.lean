module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite kernels of linear maps

This neutral support leaf records the closure of finite modules under kernels over a Noetherian
ring.  It is independent of local-ring, depth, resolution, and category-theoretic structure, so
those applications can import it directly.
-/

@[expose] public section

universe u v w

namespace LinearMap

variable {R : Type u} [Ring R] [IsNoetherianRing R]
variable {P : Type v} {Q : Type w}
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- The kernel of a linear map with finite domain is finite over a Noetherian ring.

No surjectivity or finiteness condition on the codomain is needed: the kernel is a submodule of
the finite domain. -/
@[stacks 00LX "finite kernel of a linear map with finite domain"]
instance ker_finite_of_finite [Module.Finite R P] (f : P →ₗ[R] Q) :
    Module.Finite R (ker f) := sorry

end LinearMap
