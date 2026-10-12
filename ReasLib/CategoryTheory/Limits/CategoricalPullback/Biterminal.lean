/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Biterminal
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pith
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal property of the explicit categorical pullback

The canonical categorical-pullback square is a bilimit in `Cat` and hence biterminal after
passing to the locally groupoidal pith.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open Bicategory
open CategoricalPullback
open scoped Bicategory CategoricalPullback

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable (F : A ⥤ C) (G : B ⥤ C)

namespace CategoricalPullback.catCommSqOver

/-- The categorical pullback cone is a
bilimit in the full bicategory `Cat`, before discarding noninvertible natural transformations. -/
@[instance]
theorem isBilimit :
    (catCommSqOver F G).IsBilimit := sorry
/- Proof strategy: for every categorical square `S`, use `functorEquiv F G S.pt`. Its inverse
constructs the comparison functor to `F ⊡ G`, while full faithfulness gives the unique compatible
natural transformation between any two lifts. Translate this equivalence through
`CatCommSqOver.toPseudoPullbackCone` and construct the generic
`ColaxCostructuredArrow.IsUniversal` property. -/

/-- The explicit categorical pullback square, regarded in `Pith Cat`, is biterminal. All objects
and functors in the square are unchanged; taking `Core` of each hom-category retains only
natural isomorphisms as `2`-morphisms:

```
                  π₁ F G
       F ⊡ G ─────────────────▶ A
         │                       │
  π₂ F G │                       │ F
         ▼                       ▼
         B ────────────────────▶ C
                    G
```

The statement uses the direct `CatCommSqOver.toPith` view; its biterminality follows from the
generic pith restriction of a bilimit pseudopullback cone. -/
@[stacks 02X9, instance]
theorem toPith.isBiterminal :
    Bicategory.IsBiterminal (catCommSqOver F G).toPith := sorry
/- Proof strategy: `catCommSqOver.isBilimit F G` supplies the full `Cat`-bilimit property, and
`PseudoPullbackCone.toPith.isBiterminal` applies through `CatCommSqOver.toPith`. -/

end CategoricalPullback.catCommSqOver

end CategoryTheory.Limits
