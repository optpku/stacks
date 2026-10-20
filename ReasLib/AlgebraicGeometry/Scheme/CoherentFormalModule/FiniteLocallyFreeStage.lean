/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- The `n`-th stage of a coherent formal module is finite locally free over
the quotient of the structure sheaf by the `n`-th power of its ideal sheaf. -/
def IsFiniteLocallyFreeStage {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentFormalModules X I) (n : ℕ) : Prop :=
  ∃ h_ann : (I ^ n).toSubobject ≤
      SheafOfModules.Annihilator.subobject (F.obj.obj (op n)).obj,
    SheafOfModules.IsFiniteLocallyFree
      (descendOfLE (I ^ n).toSubobject (F.obj.obj (op n)).obj h_ann)

/-- The stagewise finite-local-freeness predicate unfolds to annihilator containment
and finite local freeness of the descended quotient module. -/
theorem isFiniteLocallyFreeStage_iff {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentFormalModules X I) (n : ℕ) :
    IsFiniteLocallyFreeStage F n ↔
      ∃ h_ann : (I ^ n).toSubobject ≤
          SheafOfModules.Annihilator.subobject (F.obj.obj (op n)).obj,
        SheafOfModules.IsFiniteLocallyFree
          (descendOfLE (I ^ n).toSubobject (F.obj.obj (op n)).obj h_ann) := sorry

/-- Finite locally free coherent formal modules are those whose every natural-number stage,
including stage zero defined using the quotient by `I ^ 0`, is finite locally free. -/
def finiteLocallyFree (X : Scheme.{u}) (I : X.IdealSheafData) :
    ObjectProperty (CoherentFormalModules X I) :=
  fun F ↦ ∀ n : ℕ, IsFiniteLocallyFreeStage F n

/-- Membership in `finiteLocallyFree X I` is stagewise finite local freeness. -/
theorem finiteLocallyFree_iff (X : Scheme.{u}) (I : X.IdealSheafData)
    (F : CoherentFormalModules X I) :
    finiteLocallyFree X I F ↔ ∀ n : ℕ, IsFiniteLocallyFreeStage F n := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
