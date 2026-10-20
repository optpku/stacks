/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.LeftLegDiagonal.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilimit property of left-leg diagonal squares

This module contains the fixed-universe `Pith Cat` consequence of the ordinary left-leg
diagonal construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v u

namespace CategoricalPullback.CatCommSqOver.LeftLegDiagonal.square

variable {U : Type (max u v)} [Category.{v} U]
variable {X : Type (max u v)} [Category.{v} X]
variable {V : Type (max u v)} [Category.{v} V]
variable {Y : Type (max u v)} [Category.{v} Y]
variable {F : X ⥤ Y} {G : V ⥤ Y}

/-- If `P` is a pseudo-pullback bilimit square, then the square induced by its left leg is again
a `2`-fibre-product square:

```
                                  Δₚ P.snd
       U ─────────────────────────────────────────────▶ P.snd ⊡ P.snd
       │                                                         │
 P.fst │                                                         │ LeftLegDiagonal.map P
       ▼                                                         ▼
       X ─────────────────────────────────────────────▶ F ⊡ F
                                   Δₚ F
```
-/
@[stacks 04YR "left-leg diagonal pullback is a bilimit"]
instance isBilimit (P : CatCommSqOver F G U) [P.IsBilimit] :
    (LeftLegDiagonal.square P).IsBilimit := sorry

end CategoricalPullback.CatCommSqOver.LeftLegDiagonal.square

end CategoryTheory.Limits
