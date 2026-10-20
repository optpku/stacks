/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Parasitic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 103.9.1: let `X` be an algebraic stack. A presheaf of
`𝒪_X`-modules `F` is parasitic if `F(x) = 0` for any object `x` of `X`
which lies over a scheme `U` such that the corresponding morphism
`x : U ⟶ X` is flat. -/
@[stacks 0773] #check (AlgebraicGeometry.GroupoidsOver.IsParasitic :
  {S : AlgebraicGeometry.Scheme.{u}} →
  {X : AlgebraicGeometry.GroupoidsOver S} →
  [AlgebraicGeometry.AlgebraicStack X] →
  PresheafOfModules.{u} (AlgebraicGeometry.GroupoidsOver.structureSheaf X).obj → Prop)
