/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocallyQuasicoherent

@[expose] public section

universe u

#check (AlgebraicGeometry.GroupoidsOver.IsLocallyQuasicoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.GroupoidsOver S},
    PresheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj → Prop)
