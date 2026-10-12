/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Shift

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.instIsStableUnderShift :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (T : TopologicalSpace.Closeds X),
    (AlgebraicGeometry.Scheme.DerivedQCoh.quasiCoherentOnSupport X T).IsStableUnderShift ℤ)
