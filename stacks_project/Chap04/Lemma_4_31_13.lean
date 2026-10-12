/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalBilimit
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable {D : Type (max u v)} [Category.{v} D]
variable (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)


/- Lemma 4.31.13: for `F : A ⥤ C`, `G : B ⥤ C`, and `H : C ⥤ D`, the square

```
                            postcompose F G H
          F ⊡ G ─────────────────────────────────────────▶ (F ⋙ H) ⊡ (G ⋙ H)
            │                                                │
toBase F G  │                                                │ toDiagonal F G H
            ▼                                                ▼
            C ───────────────────────────────────────────▶ H ⊡ H
                                      Δₚ H
```

is a `2`-fibre-product diagram. -/
@[stacks 04Z1]
#check (CategoryTheory.Limits.CategoricalPullback.diagonalSquareOver.isBilimit F G H :
  (CategoricalPullback.diagonalSquareOver F G H).IsBilimit)


end CategoryTheory.Limits
