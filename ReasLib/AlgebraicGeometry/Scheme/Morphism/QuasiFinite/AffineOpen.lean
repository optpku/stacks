module

public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.FiniteSet
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Normalization

/-!
# Affine neighborhoods for locally quasi-finite morphisms

Finite subsets of the source have affine neighborhoods under suitable hypotheses on a morphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Every finite subset of the source of a separated, locally finite-type and locally
quasi-finite morphism to an affine scheme is contained in a single affine open. -/
theorem exists_affineOpen_containing_finiteSet
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [IsAffine Y] (E : Set X) (hE : E.Finite) :
    ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X) := sorry

end AlgebraicGeometry.Scheme.Hom
