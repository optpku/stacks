/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

open CategoricalPullback
open scoped CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (F : A ⥤ C) (G : B ⥤ C)
variable (x y : F ⊡ G)

/-
Mathlib 4.32's `CategoricalPullback F G` is exactly the source's iso-comma model of the
`2`-fibre product. Its objects store the triple `(a, b, e)` with
`e : F.obj a ≅ G.obj b`; its morphisms store both component maps and the compatibility
equation. This is not an ordinary `Limits.IsPullback` square inside a fixed category, and it is
not a lax comma category whose comparison cell may be noninvertible.

The existing scoped notation `F ⊡ G` is worth using: unlike an item-local notation modeled on
`A ×_C B`, it keeps the two defining functors visible and agrees with the canonical mathlib owner.
No parallel triple structure, projection wrapper, or new notation is introduced.

The canonical square has the following direction:

```
                  π₁ F G
       F ⊡ G ─────────────────▶ A
         │                       │
  π₂ F G │                       │ F
         ▼                       ▼
         B ────────────────────▶ C
                    G
```

It commutes up to the canonical natural isomorphism
`(catCommSq F G).iso : π₁ F G ⋙ F ≅ π₂ F G ⋙ G`, in the same left-to-right
direction as the source transformation `ψ`.

Import decision: `Categorical.Basic` is public because every labeled surface exposes its data.
The reusable explicit bundled square lives in
`CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`, so this source-facing recall file does
not own downstream infrastructure. `Definition_4_31_2` is deliberately not imported: later
bicategorical comparisons import that infrastructure directly. `StacksCheckRecall` is plain
because it only elaborates the source annotations.
-/

/- Example 4.31.3 (1): an object of the `2`-fibre product of `F : A ⥤ C` and `G : B ⥤ C`
is the canonical triple in `CategoricalPullback F G`, consisting of `a : A`, `b : B`, and an
isomorphism `F.obj a ≅ G.obj b`. -/
@[stacks 003R "objects as triples with a structural isomorphism"]
#check (CategoricalPullback F G : Type max u₁ u₂ v₃)

/- Example 4.31.3 (2): a morphism `φ : x ⟶ y` in `CategoricalPullback F G` is a compatible
pair displayed by

```
                         x.iso.hom
       F.obj x.fst ─────────────────────▶ G.obj x.snd
             │                                  │
 F.map φ.fst │                                  │ G.map φ.snd
             ▼                                  ▼
       F.obj y.fst ─────────────────────▶ G.obj y.snd
                         y.iso.hom
```

Thus the stored equation has the source's orientation:
`F.map φ.fst ≫ y.iso.hom = x.iso.hom ≫ G.map φ.snd`. -/
@[stacks 003R "morphisms as compatible pairs"]
#check (CategoricalPullback.Hom x y : Type max v₁ v₂)

/- Example 4.31.3 (3): the first forgetful functor is the canonical projection
`CategoricalPullback.π₁`. -/
@[stacks 003R "first forgetful projection functor"]
#check (CategoricalPullback.π₁ F G : F ⊡ G ⥤ A)

/- Example 4.31.3 (4): the second forgetful functor is the canonical projection
`CategoricalPullback.π₂`. -/
@[stacks 003R "second forgetful projection functor"]
#check (CategoricalPullback.π₂ F G : F ⊡ G ⥤ B)

/- Example 4.31.3 (5): `CategoricalPullback.catCommSq` supplies the natural isomorphism between
the two projection composites. Its forward natural transformation is the source's `ψ`. -/
@[stacks 003R "natural isomorphism between the projection composites"]
#check (CategoricalPullback.catCommSq F G :
  CatCommSq (CategoricalPullback.π₁ F G) (CategoricalPullback.π₂ F G) F G)

end CategoryTheory.Limits
