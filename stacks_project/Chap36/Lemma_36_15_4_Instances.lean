/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Shift

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.instIsStableUnderShift :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (T : TopologicalSpace.Closeds X),
    (AlgebraicGeometry.Scheme.DerivedQCoh.quasiCoherentOnSupport X T).IsStableUnderShift ℤ)
