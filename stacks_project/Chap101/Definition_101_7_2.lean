/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 101.7.2: a morphism `f : X ⟶ Y` of algebraic stacks is
quasi-compact if for every quasi-compact algebraic stack `Z` and morphism
`Z ⟶ Y`, the fibre product `Z ×_Y X` is a quasi-compact algebraic stack.

Stacks writes `Z ×_Y X`; the Lean test uses a `PseudoPullbackCone f g` with
`fst : P ⟶ X` and `snd : P ⟶ Z`. -/
@[stacks 050U] #check (AlgebraicGeometry.AlgebraicStack.QuasiCompact :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    [AlgebraicGeometry.AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack Y],
    (X ⟶ Y) → Prop)
