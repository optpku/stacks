/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

open CategoryTheory AlgebraicGeometry

/- 97.10.0.2: For morphisms `Z ⟶ B` and `X ⟶ B` of algebraic spaces over a
scheme `S`, `Mor_B(Z, X)` is the functor `(Over S)ᵒᵖ ⥤ Type (u + 1)` sending a
scheme `T` over `S` to the type of pairs `(a, b)` with `a : ofOver T ⟶ B` and
`b` a morphism over `ofOver T` from `pullback a g` to `pullback a h`, where
`g : Z ⟶ B` and `h : X ⟶ B`; these pairs form `RelativeHom.Pair g h T`. -/
@[stacks 05Y2] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.presheaf :
  ∀ {S : Scheme.{u}} {Z X B : AlgebraicSpace S},
    (Z ⟶ B) → (X ⟶ B) → (Over S)ᵒᵖ ⥤ Type (u + 1))
