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
variable {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)

/- Mathlib's `IsPushout f g inl inr` is the source-facing owner: it packages both the
commutativity witness and the colimit property of the associated `PushoutCocone`. The lower-level
`IsColimit (PushoutCocone.mk inl inr h)` requires a separately chosen commutativity proof, while
`Square.IsPushout` first bundles the same four maps into a `Square`. Thus `IsPushout` recovers the
source without generalization and directly exposes the standard descent and hom-extensionality API
for downstream use. -/

/-
Definition 4.9.2: a commutative square

```
      y ───────────▶ z
      │              │
      ▼              ▼
      x ───────────▶ w
```

in a category is cocartesian if `w` together with the morphisms `x ⟶ w` and `z ⟶ w` forms a
pushout of `y ⟶ x` and `y ⟶ z`. This is exactly the canonical mathlib notion `IsPushout`.
-/
@[stacks 08N1 "cocartesian square as a commutative pushout square"]
#check (IsPushout f g inl inr : Prop)

/- Companion recall: the canonical cocartesian-square notion exposes its commutative square via
`IsPushout.toCommSq`. -/
#check IsPushout.toCommSq

end CategoryTheory
