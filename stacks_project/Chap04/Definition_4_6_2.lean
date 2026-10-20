/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)

/-
Definition 4.6.2: a commutative square

```
      w ───────────▶ z
      │              │
      ▼              ▼
      x ───────────▶ y
```

in a category is cartesian if `w` together with the morphisms `w ⟶ x` and `w ⟶ z` forms a fibre
product of `x ⟶ y` and `z ⟶ y`. This is the canonical mathlib notion `IsPullback`; the bundled
square view `Square.IsPullback` is only a packaging layer on top of it. -/
@[stacks 08N0 "cartesian square as a pullback of its right and bottom morphisms"]
#check (IsPullback fst snd f g : Prop)

end CategoryTheory
