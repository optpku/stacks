module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Shift

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.instIsStableUnderShift :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (T : TopologicalSpace.Closeds X),
    (AlgebraicGeometry.Scheme.DerivedQCoh.quasiCoherentOnSupport X T).IsStableUnderShift ℤ)
