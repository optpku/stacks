/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 76.52.6: for a scheme `S` and a flat, locally finitely presented morphism
`f : X ⟶ Y` of algebraic spaces over `S`, arbitrary base change `g : Y' ⟶ Y`
preserves `Y`-perfectness: if `K` in `D(𝒪_X)` is `Y`-perfect, then
`L(g')* K` is `Y'`-perfect, where `X' = Y' ×_Y X` and `g' : X' ⟶ X` is the
projection. -/
@[stacks 0DKT] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo.baseChange :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
      (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (g : Y' ⟶ Y)
      (K : ModuleDerived X),
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo f K →
        AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo
          (pullback.snd f g)
          ((AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullback (pullback.fst f g)).obj K))
