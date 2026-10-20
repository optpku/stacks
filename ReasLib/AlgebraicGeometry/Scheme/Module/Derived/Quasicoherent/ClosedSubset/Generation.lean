/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Shift
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

/-- If `X` is quasi-compact and quasi-separated and `T` has quasi-compact complement, then the
category of derived quasi-coherent modules supported on `T` has a perfect weak generator. -/
theorem exists_isPerfect_isWeakGenerator {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) :
    ∃ P : SupportedOn X T,
      RingedSpace.ModuleDerived.IsPerfect P.obj.obj ∧ IsWeakGenerator P := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
