/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.Ext

/-!
# Representations of Ext delta functors

This module records when an explicit derived module represents an Ext delta functor on
quasicoherent coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace ProjectionFormula

/-- A derived module `L` represents an Ext delta functor when there is a boundary-compatible
comparison from `representedExtDelta S L` to `extDelta f E G` that is invertible in every
degree. -/
def RepresentsExt {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    (L : RingedSpace.ModuleDerived S.toRingedSpace)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)] : Prop :=
  ∃ comparison : CohomologyTransform
      (representedExtDelta S L) (extDelta f E G),
    ∀ i : ℤ, IsIso (comparison.app i)

/-- A derived module represents an Ext delta functor exactly when it admits a
boundary-compatible, degreewise invertible comparison from the represented functor. -/
theorem representsExt_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ)
    (L : RingedSpace.ModuleDerived S.toRingedSpace)
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)] :
    RepresentsExt f E G L ↔
      ∃ comparison : CohomologyTransform
          (representedExtDelta S L) (extDelta f E G),
        ∀ i : ℤ, IsIso (comparison.app i) := sorry

end ProjectionFormula
end ModuleDerived
end Scheme
end AlgebraicGeometry
