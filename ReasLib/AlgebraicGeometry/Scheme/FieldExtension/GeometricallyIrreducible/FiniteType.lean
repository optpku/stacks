module

public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Irreducible

/-!
# Finite-type approximation of geometrically irreducible field extensions

Every finite subset of a geometrically irreducible extension of a finite field
lies in a geometrically irreducible finite-type subalgebra.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FieldExtension.GeometricallyIrreducible

/-- Every finite subset of a geometrically irreducible extension of a finite field
is contained in a finite-type subalgebra whose spectrum is geometrically irreducible
over the base field. -/
@[stacks 0BA7]
theorem exists_finiteType_subalgebra {k K : Type u} [Field k] [Finite k] [Field K]
    [Algebra k K] [GeometricallyIrreducible (FieldExtension.specMap k K)]
    (s : Finset K) :
    ∃ (A : Subalgebra k K),
      Algebra.FiniteType k A ∧
        GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))) ∧
          (s : Set K) ⊆ A :=
  sorry

end AlgebraicGeometry.FieldExtension.GeometricallyIrreducible
