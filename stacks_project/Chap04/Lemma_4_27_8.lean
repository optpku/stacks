/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import StacksCheckRecall

@[expose] public section

universe v u vE uE

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y : C} (s : X ⟶ Y) (hs : W s)
variable (E : Type uE) [Category.{vE} E]

/- The source uses the concrete left-fraction model, not merely a localization chosen up to
equivalence. Mathlib's `MorphismProperty.LeftFraction.Localization.Q`, `Qiso`, and
`strictUniversalPropertyFixedTarget` exactly own its three clauses. Writing `W⁻¹C` for
`LeftFraction.Localization W`, the last clause is the strict commutative square

```
                    Q W
       C ─────────────────────▶ W⁻¹C
       │                         │
     F │                         │ H
       ▼                         ▼
       E ─────────────────────▶ E
                    𝟭 E
```

with `(Q W) ⋙ H = F`. The fixed target `E` is universe-polymorphic, and `uniq` is equivalent to
the source's uniqueness among functors satisfying this equality. The companion
`Functor.IsLocalization` instance is the invariant downstream abstraction, but does not replace
the source-facing strict owner. -/

/- Lemma 4.27.8 (1): for a left multiplicative system `W`, the rules `X ↦ X` and
`f : X ⟶ Y ↦ (f, 𝟙 Y)` define the canonical functor from `C` to the left-fraction localization. -/
@[stacks 04VG "canonical left-fraction localization functor"]
#check (MorphismProperty.LeftFraction.Localization.Q W :
  C ⥤ MorphismProperty.LeftFraction.Localization W)

/- Lemma 4.27.8 (2): the canonical localization functor sends every morphism in `W` to an
isomorphism. -/
@[stacks 04VG "morphisms in the system become isomorphisms"]
#check (MorphismProperty.LeftFraction.Localization.Qiso s hs :
  (MorphismProperty.LeftFraction.Localization.Q W).obj X ≅
    (MorphismProperty.LeftFraction.Localization.Q W).obj Y)

/- Lemma 4.27.8 (3): every functor out of `C` that inverts `W` factors uniquely, with strict
equality, through the canonical left-fraction localization functor. -/
@[stacks 04VG "strict existence and uniqueness of the localization factorization"]
#check (MorphismProperty.LeftFraction.Localization.strictUniversalPropertyFixedTarget W E :
  Localization.StrictUniversalPropertyFixedTarget
    (MorphismProperty.LeftFraction.Localization.Q W) W E)

end CategoryTheory
