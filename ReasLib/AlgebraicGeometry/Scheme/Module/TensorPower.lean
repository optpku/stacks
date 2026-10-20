/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

/-!
# Integral tensor powers of invertible scheme modules

This is the scheme-facing specialization of the ringed-space autoequivalence
model.  It keeps the `Invertible` interface and the resulting tensor twist in
one narrow import for cohomology and projectivity arguments.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The integral tensor power of an invertible scheme module, defined by the
corresponding tensor-right autoequivalence applied to the structure module. -/
noncomputable def tensorPowerInt
    (L : X.Modules) [Invertible L] (d : ℤ) : X.Modules :=
  MonoidalCategory.InvertiblePower.eval L
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) d

/-- The autoequivalence expression defining `tensorPowerInt`. -/
theorem tensorPowerInt_def
    (L : X.Modules) [Invertible L] (d : ℤ) :
    tensorPowerInt L d =
      (((tensorRight L).asEquivalence ^ d).functor.obj
        (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := sorry

/-- The twist of a scheme module by an integral tensor power of an invertible
scheme module. -/
noncomputable def twistByTensorPower
    (L F : X.Modules) [Invertible L] (d : ℤ) : X.Modules :=
  tensorObj F (tensorPowerInt L d)

/-- The tensor-product expression defining `twistByTensorPower`. -/
theorem twistByTensorPower_def
    (L F : X.Modules) [Invertible L] (d : ℤ) :
    twistByTensorPower L F d = tensorObj F (tensorPowerInt L d) := sorry

/-- Every integral tensor power of an invertible scheme module is invertible. -/
@[instance]
theorem tensorPowerInt_isInvertible
    (L : X.Modules) [Invertible L] (d : ℤ) :
    Invertible (tensorPowerInt L d) := sorry

end AlgebraicGeometry.Scheme.Modules
