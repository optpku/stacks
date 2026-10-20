/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Construction
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Determinant

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace ActualTate

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f]
variable [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]

/-- The fixed global determinant of the actual naive cotangent complex,
constructed from its affine finite-projective determinants and transition maps. -/
def detNL : Y.Modules :=
  ActualGlobalDeterminant.lineSheaf Y (Scheme.Hom.Tate.cotangentObject f)

theorem cotangentRankZero [LocallyQuasiFinite f] :
    ActualGlobalDeterminant.isRankZero Y (Scheme.Hom.Tate.cotangentObject f) := by sorry

/-- The actual compatible family of exterior-differential determinant elements. -/
def delta [LocallyQuasiFinite f] : (detNL f).sections :=
  ActualGlobalDeterminant.delta Y (Scheme.Hom.Tate.cotangentObject f) (cotangentRankZero f)

/-- The canonical affine-section comparison is projection of the constructed
compatible family, rather than an independently chosen affine isomorphism. -/
def affineSectionsIso (U : Y.affineOpens) :=
  ActualGlobalDeterminant.affineSectionsIso Y (Scheme.Hom.Tate.cotangentObject f) U

end ActualTate
