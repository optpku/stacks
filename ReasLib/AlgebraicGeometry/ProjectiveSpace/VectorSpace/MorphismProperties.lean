module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.FiniteType

/-! # Finite type of projective vector spaces

A finite basis identifies the symmetric algebra with a polynomial algebra in finitely many
variables. The native finite-type theorem for Proj then applies to the existing structure map.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The structure morphism of a finite-dimensional projective vector space is locally of
finite type, including the projective scheme of the zero vector space. -/
instance toSpec_locallyOfFiniteType : LocallyOfFiniteType (toSpec k V) := by
  letI : Algebra.FiniteType k (SymmetricAlgebra k V) :=
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType k
      (MvPolynomial (Fin (Module.finrank k V)) k))
      (SymmetricAlgebra.equivMvPolynomial (Module.finBasis k V)).symm
  letI : IsScalarTower k (grading k V 0) (SymmetricAlgebra k V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FiniteType (grading k V 0) (SymmetricAlgebra k V) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (grading k V 0)
      (SymmetricAlgebra k V)
  unfold toSpec
  infer_instance

end AlgebraicGeometry.ProjectiveSpace.VectorSpace
