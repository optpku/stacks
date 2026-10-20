module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Decompositions of graded modules

A graded module is an ambient module together with a direct-sum decomposition indexed by its
degrees.
-/

@[expose] public section

universe u v

namespace GradedModule

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/-- A graded module decomposition is a direct-sum decomposition of `M` by its degree pieces. -/
abbrev Decomposition (ℳ : ℤ → Submodule A M) := DirectSum.Decomposition ℳ

end GradedModule
