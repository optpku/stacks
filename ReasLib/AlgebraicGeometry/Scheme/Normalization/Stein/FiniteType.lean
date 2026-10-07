module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PointsOver

/-!
# Finite-type relative Stein normalization

This file records finiteness properties of point fibers and residue fields for
relative normalizations of locally finite type morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The relative normalization of a quasi-separated, universally closed, locally finite type
scheme morphism has finite point fibers. -/
theorem fromNormalization_fiberFinite
    (f : X ⟶ S) [QuasiSeparated f] [UniversallyClosed f] [LocallyOfFiniteType f]
    (s : S) :
    Set.Finite (f.fromNormalization.pointsOver s) := sorry

/-- At a point over the base under the relative normalization morphism, the residue field is
finite as a module over the residue field of the base point. -/
instance instModuleFiniteResidueFieldFromNormalization
    (f : X ⟶ S) [QuasiSeparated f] [UniversallyClosed f] [LocallyOfFiniteType f]
    (s : S) (s' : f.fromNormalization.pointsOver s) :
    Module.Finite (S.residueField s) (f.normalization.residueField s') := sorry

end AlgebraicGeometry.Scheme.Hom
