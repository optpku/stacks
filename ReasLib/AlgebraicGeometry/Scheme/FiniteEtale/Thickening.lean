/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Base change along a thickening of schemes induces an equivalence between
the categories of finite étale schemes over its codomain and its domain. -/
instance finiteEtaleBaseChangeIsEquivalenceOfThickening
    {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i] :
    Functor.IsEquivalence (Scheme.finiteEtaleBaseChange i) := sorry

end AlgebraicGeometry.Scheme
