/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The chosen right adjoint to the inclusion of derived modules with quasicoherent cohomology
carries the canonical shift comparison induced by its adjunction. -/
noncomputable instance inclusionRightAdjointCommShift (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint).CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint
    (Scheme.ModuleDerived.Quasicoherent.inclusion X)).rightAdjointCommShift ℤ

/-- The chosen right adjoint to the inclusion of derived modules with quasicoherent cohomology
is an exact functor. -/
instance inclusionRightAdjointIsTriangulated (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint).IsTriangulated := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
