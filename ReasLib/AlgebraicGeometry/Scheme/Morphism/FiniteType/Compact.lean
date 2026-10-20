module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Compactness over a field for finite-type scheme morphisms

This leaf exposes the topological compactness consequence of the project-level finite-type
condition over an affine field spectrum.  It is kept separate from the finite-type definition so
that geometric applications can import the consequence without importing unrelated operations.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite-type scheme over a field has a compact underlying topological space. -/
theorem compactSpace_of_finiteType_over_field
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [FiniteType f] : CompactSpace X := sorry

end AlgebraicGeometry.Scheme.Hom
