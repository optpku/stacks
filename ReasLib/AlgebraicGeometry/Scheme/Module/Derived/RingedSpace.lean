module

public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The identity-on-data comparison from scheme modules to modules on the underlying ringed
space preserves zero morphisms. -/
instance toRingedSpacePreservesZeroMorphisms (X : Scheme.{u}) :
    (toRingedSpace X).PreservesZeroMorphisms := sorry

end AlgebraicGeometry.Scheme.Modules

namespace ModuleCech

/-- The derived realization of a nonnegative complex of scheme modules, after applying the
canonical comparison with modules on the underlying ringed space. -/
noncomputable def toRingedSpaceDerived (X : Scheme.{u}) :
    CochainComplex X.Modules ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace :=
  (Scheme.Modules.toRingedSpace X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    CochainComplex.Nat.toDerived X.toRingedSpace.Modules

/-- A module sheaf viewed as a derived module concentrated in degree zero. -/
noncomputable def moduleToDerived (X : Scheme.{u}) :
    X.Modules ⥤ RingedSpace.ModuleDerived X.toRingedSpace :=
  CochainComplex.single₀ X.Modules ⋙ toRingedSpaceDerived X

end ModuleCech

end
