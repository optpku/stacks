/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 35.12.1 (1): a presheaf of modules on the big standard site over
`S` is parasitic one when it vanishes on every scheme flat over `S`. -/
@[stacks 06ZL] #check (PresheafOfModules.IsParasiticOne :
  {S : AlgebraicGeometry.Scheme.{u}} →
    PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf) → Prop)

/- Definition 35.12.1 (2): a presheaf of modules on the big `τ`-site over `S`
is parasitic for `τ` when it vanishes on every member of every `τ`-cover of
`S`. -/
@[stacks 06ZL] #check (PresheafOfModules.IsParasitic :
  {S : AlgebraicGeometry.Scheme.{u}} →
    PresheafOfModules.{u} (ringPresheaf S.overStructurePresheaf) →
      AlgebraicGeometry.StandardTopology → Prop)
