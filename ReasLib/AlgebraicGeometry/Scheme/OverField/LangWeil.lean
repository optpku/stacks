module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Data.Finite.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.FiniteType

/-!
# Field-valued points from Lang–Weil estimates

A geometrically irreducible finite-type algebra over a finite field admits a map
to a field extension of each sufficiently large degree.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible

/-- A geometrically irreducible finite-type algebra over a finite field admits an
algebra homomorphism to a finite extension of each sufficiently large degree. -/
@[stacks 0BA7]
theorem exists_algHom_degree {k A : Type u} [Field k] [Finite k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (f : A →ₐ[k] k'),
        FiniteDimensional k k' ∧ Module.finrank k k' = n :=
  sorry

end AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible
