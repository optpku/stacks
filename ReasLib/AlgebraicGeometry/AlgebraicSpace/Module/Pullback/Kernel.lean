/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Zero morphisms under module pullback -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient

/-- Module pullback of algebraic spaces preserves zero morphisms. -/
instance preservesZeroMorphisms_modulesPullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Modules.pullback f).PreservesZeroMorphisms := sorry

end AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient
