/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity of differentials for formally smooth algebraic-space morphisms

For composable morphisms of algebraic spaces, formal smoothness of the first
morphism makes the canonical transitivity sequence of relative differentials
short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Hom.Differentials.Transitivity

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace FormallySmooth

/-- For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces
over a scheme, formal smoothness of `f` makes the canonical transitivity sequence
`0 ⟶ f^* Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` short exact. -/
@[stacks 06BI]
theorem relativeDifferentialsTransitivity_shortExact
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallySmooth f] :
    (complex f g).ShortExact :=
  sorry

end FormallySmooth
end AlgebraicGeometry.AlgebraicSpace
