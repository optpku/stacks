/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cospan transformations from invertible comparison cells

This module owns the constructor assembling a categorical cospan transformation from the two
invertible faces of a vertical cospan diagram.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

namespace Limits.CatCospanTransform

variable {H : X ⥤ Z} {I : Y ⥤ Z} {L : X ⥤ A} {K : Y ⥤ B}
variable {M : Z ⥤ C} {F : A ⥤ C} {G : B ⥤ C}

/-- Chosen invertible `2`-cells on the two faces of a vertical cospan diagram
determine a categorical cospan transformation:

```
              H                   I
       X ───────────▶ Z ◀─────────── Y
       │              │               │
     L │            M │             K │
       ▼              ▼               ▼
       A ───────────▶ C ◀─────────── B
              F                   G
```

For cells `α : K ⋙ G ≅ I ⋙ M` and `β : H ⋙ M ≅ L ⋙ F`, the
induced functor is
`CategoricalPullback.map (CatCospanTransform.ofIso β α.symm)`. On an object
`(x, y, φ)`, its structural isomorphism is
`β.symm.app x ≪≫ M.mapIso φ ≪≫ α.symm.app y`; the component maps on morphisms are
`L.map` and `K.map`. -/
@[stacks 02XA "cospan transformation from invertible comparison cells"]
def ofIso (squareLeft : H ⋙ M ≅ L ⋙ F) (squareRight : I ⋙ M ≅ K ⋙ G) :
    CatCospanTransform H I F G where
  left := L
  base := M
  right := K
  squareLeft := ⟨squareLeft⟩
  squareRight := ⟨squareRight⟩

end Limits.CatCospanTransform

end CategoryTheory

/- Axiom audit: the cospan transformation is assembled from explicit functor and isomorphism data. -/
