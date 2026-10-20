/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Tate

/-- The derived naive cotangent complex of a syntomic morphism is perfect. -/
theorem cotangentPerfect {X Y : Scheme.{u}} (f : Y ⟶ X) [Syntomic f] :
    RingedSpace.ModuleDerived.IsPerfect
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) := sorry

/-- The derived naive cotangent complex of a syntomic morphism has Tor-amplitude in
`[-1, 0]`. -/
theorem cotangentTorAmplitude {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)] [Syntomic f] :
    RingedSpace.HasTorAmplitudeIn
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0 := sorry

/-- The derived naive cotangent complex, bundled in the domain of a determinant
construction. -/
noncomputable def cotangentObject {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)] [Syntomic f] :
    PerfectDerived.TorNegOneZero Y :=
  ⟨⟨(DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom) :
      Y.toRingedSpace.ModuleDerived), cotangentPerfect f⟩,
    cotangentTorAmplitude f⟩

/-- Forgetting the perfectness and Tor-amplitude witnesses recovers the derived naive
cotangent complex. -/
theorem cotangentObject_obj {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)] [Syntomic f] :
    (cotangentObject f).obj.obj =
      (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom) :
        Y.toRingedSpace.ModuleDerived) := sorry

/-- The naive cotangent object of a locally quasi-finite syntomic morphism has determinant
rank zero. -/
theorem cotangentRankZero {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) :
    D.isRankZero (cotangentObject f) := sorry

/-- The canonical section of the determinant line of the derived naive cotangent complex. -/
noncomputable def delta {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) :
    (D.line (cotangentObject f)).sections :=
  RingedSpace.sectionFromTop (D.line (cotangentObject f))
    (D.canonicalElement (cotangentObject f) (cotangentRankZero f D))

/-- The determinant section is obtained from the canonical top-open determinant element. -/
theorem delta_def {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) :
    delta f D = RingedSpace.sectionFromTop (D.line (cotangentObject f))
      (D.canonicalElement (cotangentObject f) (cotangentRankZero f D)) := sorry

/-- A determinant-line isomorphism is a Tate isomorphism when it carries the canonical
determinant section to the specified section of the target module. -/
def IsTateIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) (W : Y.Modules)
    (τ : W.sections) (c : D.line (cotangentObject f) ≅ W) : Prop :=
  SheafOfModules.sectionsMap c.hom (delta f D) = τ

/-- The Tate-isomorphism predicate is exactly preservation of the distinguished section. -/
theorem isTateIso_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [LocallyQuasiFinite f] [Syntomic f]
    (D : PerfectDerived.TorNegOneZero.Determinant Y) (W : Y.Modules)
    (τ : W.sections) (c : D.line (cotangentObject f) ≅ W) :
    IsTateIso f D W τ c ↔
      SheafOfModules.sectionsMap c.hom (delta f D) = τ := sorry

end AlgebraicGeometry.Scheme.Hom.Tate
