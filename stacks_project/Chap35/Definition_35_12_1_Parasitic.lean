/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic

@[expose] public section

universe u

#check (PresheafOfModules.IsParasiticOne :
  {S : AlgebraicGeometry.Scheme.{u}} →
    PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf) → Prop)

#check (PresheafOfModules.IsParasitic :
  {S : AlgebraicGeometry.Scheme.{u}} →
    PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf) →
      AlgebraicGeometry.StandardTopology → Prop)
