/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal subobjects of ringed spaces

This file owns ideal sheaves as subobjects of the structure module.  Kernel,
pullback, and local-generation APIs live in focused submodules.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

/-- An ideal subobject of a ringed space is a subobject of its structure sheaf, viewed as a
module over itself. -/
@[stacks 01C2 "ringed-space ideal subobject"]
abbrev IdealSubobject (X : RingedSpace.{u}) : Type (u + 1) :=
  Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- The module sheaf represented by an ideal subobject. -/
@[stacks 01C2 "ideal subobject module"]
noncomputable abbrev IdealSubobject.toModule {X : RingedSpace.{u}}
    (I : IdealSubobject X) : X.Modules :=
  Subobject.underlying.obj I

end AlgebraicGeometry.RingedSpace
