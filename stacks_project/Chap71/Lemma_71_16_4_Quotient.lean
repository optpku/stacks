/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Kernel
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertibleQuotient.Conormal

/-! # Pullback of quotient kernels on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient.preservesZeroMorphisms_modulesPullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (AlgebraicSpace.Modules.pullback f).PreservesZeroMorphisms)
