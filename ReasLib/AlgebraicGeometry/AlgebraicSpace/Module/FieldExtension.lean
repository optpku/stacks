/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GenericFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Field-extension base change of modules on algebraic spaces

An extension of fields induces pullback of module sheaves along the projection
from the base-changed algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension

/-- The pullback of an `𝒪_X`-module to a field-extension base change. -/
abbrev baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules) :
    (GenericFiber.baseChange k K X).Modules :=
  (pullback (GenericFiber.toSource k K X)).obj F

/-- Module base change along a field extension is pullback along the source projection. -/
theorem baseChange_eq (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules) :
    baseChange k K F = (pullback (GenericFiber.toSource k K X)).obj F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension
