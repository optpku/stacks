module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support
public import Mathlib.CategoryTheory.ObjectProperty.Shift

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- Derived quasi-coherent modules supported on a subset are stable under shifts. -/
instance instIsStableUnderShift {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Points X)) :
    (quasiCoherentSupportedOn X T).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := by sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
