/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Topology
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.38.6: Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact morphism of algebraic
stacks. Let `𝒵 ⊂ 𝒴` be a scheme-theoretic image of `f`. Then `|𝒵|` is the
closure of the image of `|f|`. -/
@[stacks 0CML] #check
  (AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage.closure_range_eq :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
      (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage f toImage ι],
      closure (Set.range (AlgebraicGeometry.AlgebraicStack.Points.map f)) =
        Set.range (AlgebraicGeometry.AlgebraicStack.Points.map ι))
