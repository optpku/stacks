/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes
import StacksCheckRecall

universe u

/- Definition 75.14.2: for a scheme `S` and algebraic space `X` over `S`, approximation
by perfect complexes holds on `X` when every closed subset `T` of `Points X` whose
open complement immersion `OpenSubspace.ofOpensι T.compl` is quasi-compact admits an
integer `r` such that every triple `(T, E, m)` as in `HasPerfectApproximation` with
`E` `(m - r)`-pseudo-coherent and `Hⁱ(E)` supported on `T` for `i ≥ m - r` has a
perfect approximation. -/
@[stacks 08HJ] #check
  (AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes :
    {S : AlgebraicGeometry.Scheme.{u}} →
      AlgebraicGeometry.AlgebraicSpace S → Prop)
