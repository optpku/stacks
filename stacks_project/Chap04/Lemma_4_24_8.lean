/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe vC uC vD uD

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
variable (alpha : L₂ ⟶ L₁) (d : D)

/- Lemma 4.24.8: let `adj₁ : U₁ ⊣ V₁`, `adj₂ : U₂ ⊣ V₂`, and
`β : U₂ ⟶ U₁`. The right mate is owned by the canonical equivalence
`βᵛ := conjugateEquiv adj₁ adj₂ β : V₁ ⟶ V₂`; no separate local transformation
wrapper is needed. Its compatibility with the two counits is the commutative functor square

```
                         V₁ ◁ β
       V₁ ⋙ U₂ ─────────────────────▶ V₁ ⋙ U₁
              │                              │
      βᵛ ▷ U₂ │                              │ adj₁.counit
              ▼                              ▼
       V₂ ⋙ U₂ ─────────────────────▶ 𝟭 D
                       adj₂.counit
```

Thus at `d : D` one has
`U₂.map (βᵛ.app d) ≫ adj₂.counit.app d =
  β.app (V₁.obj d) ≫ adj₁.counit.app d`.
This is exactly `conjugateEquiv_counit`. The more general theorem
`mateEquiv_counit` allows nonidentity vertical functors; `conjugateEquiv_counit` is the faithful
specialization to the source statement and hence the lighter public surface here.
The canonical proof route is to regard `conjugateEquiv` as the identity-vertical specialization
of `mateEquiv`, apply `mateEquiv_counit`, and simplify the unitors componentwise; mathlib already
provides that result, so this item carries no local proof debt.

`Mathlib.CategoryTheory.Adjunction.Mates` is public because this recalled theorem is the item's
exported API. `StacksCheckRecall` remains plain because it is needed only by the diagnostic
`recall` command. -/
@[stacks 0B65 "counit square for conjugate transformations of right adjoints"]
#check (conjugateEquiv_counit adj₁ adj₂ alpha d :
  L₂.map ((conjugateEquiv adj₁ adj₂ alpha).app d) ≫ adj₂.counit.app d =
    alpha.app (R₁.obj d) ≫ adj₁.counit.app d)

end CategoryTheory
