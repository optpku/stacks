/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
