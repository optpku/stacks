/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.UniversalHomeomorphism

@[expose] public section

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.WeaklyEtale.instIsIsoOfUniversalHomeomorphism :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.WeaklyEtale f] [AlgebraicGeometry.UniversalHomeomorphism f],
        IsIso f)
