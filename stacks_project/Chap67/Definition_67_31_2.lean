/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Definition 67.31.2 (1): let `S` be a scheme, `f : X ⟶ Y` a morphism of algebraic
spaces over `S`, and `F` a quasi-coherent sheaf on `X`. For `x ∈ |X|` (`Points X`),
we say `F` is flat at `x` over `Y` if the equivalent conditions of Lemma 67.31.1 hold. -/
@[stacks 05VV] #check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    X.Modules → (X ⟶ Y) → AlgebraicSpace.Points X → Prop)

/- Definition 67.31.2 (2): with the same standing data, we say `F` is flat over `Y`
if `F` is flat over `Y` at every `x ∈ |X|`. -/
@[stacks 05VV] #check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, X.Modules → (X ⟶ Y) → Prop)
