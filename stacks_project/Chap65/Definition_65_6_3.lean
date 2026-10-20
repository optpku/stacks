/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 65.6.3: for algebraic spaces `F`, `F'` over a scheme `S`, a morphism
`f : F ⟶ F'` of algebraic spaces over `S` is a transformation of functors from `F`
to `F'`. -/
@[stacks 0260] #check (AlgebraicGeometry.AlgebraicSpace.Hom :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S →
    AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
