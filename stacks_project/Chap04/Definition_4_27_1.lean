module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/- Mathlib's `HasLeftCalculusOfFractions` and `HasRightCalculusOfFractions` are the exact
source-facing owners. Both extend `IsMultiplicative`, which is precisely MS1. Their fraction
completion fields encode MS2 with the following arrow directions:

```
Left calculus (given: t, g; chosen: s, f):

                  g
       X' ─────────────────▶ Y
        │                    │
  t ∈ W │                    │ s ∈ W
        ▼                    ▼
        X ─────────────────▶ Y'
                  f

Right calculus (given: s, f; chosen: t, g):

                  g
       X' ─────────────────▶ Y
        │                    │
  t ∈ W │                    │ s ∈ W
        ▼                    ▼
        X ─────────────────▶ Y'
                  f
```

On the left, `t` and `g` are given and `s` and `f` are supplied; on the right, `s` and `f`
are given and `t` and `g` are supplied. In both diagrams commutativity is `g ≫ s = t ≫ f`. The two
`ext` fields are exactly MS3: left calculus turns an equality after precomposition by a
denominator into one after postcomposition, and right calculus does the converse. This also
explains why passage to `W.op` exchanges the two canonical classes.

The installed localization API has no separate owner for having both calculi, and the nLab
localization interface likewise treats the two calculi independently (with both available when
both fraction descriptions are needed). Thus the final source notion is exposed as their direct
conjunction. A new class or notation would only duplicate the canonical typeclass inputs used by
downstream localization theorems and would make instance search less transparent.
-/

/- Definition 4.27.1 (1): a left multiplicative system is exactly a morphism property with a left
calculus of fractions. -/
@[stacks 04VC "left multiplicative systems"]
#check (W.HasLeftCalculusOfFractions : Prop)

/- Definition 4.27.1 (2): a right multiplicative system is exactly a morphism property with a
right calculus of fractions. -/
@[stacks 04VC "right multiplicative systems"]
#check (W.HasRightCalculusOfFractions : Prop)

/- Definition 4.27.1 (3): a multiplicative system is both a left and a right multiplicative
system. -/
@[stacks 04VC "multiplicative systems have both calculi of fractions"]
#check (W.HasLeftCalculusOfFractions ∧ W.HasRightCalculusOfFractions : Prop)

end MorphismProperty
end CategoryTheory
