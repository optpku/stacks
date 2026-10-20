module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Symmetric
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilimit criteria for categorical pullback squares

A categorical commutative square is a pseudo-pullback bilimit exactly when its canonical
comparison to the explicit categorical pullback is an equivalence.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory.Limits

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v u

/-
Design note: the source works in the pith of `Cat`. Its objects are arbitrary categories; only
the `2`-morphisms between functors are restricted to natural isomorphisms. Thus imposing
`IsGroupoid` on `A`, `B`, `S`, or the apex would change the theorem rather than formalize
its `(2, 1)`-categorical setting.

The canonical comparison functor is `CatCommSqOver.comparison`, built from mathlib's
`CategoricalPullback.functorEquiv`. The source's "canonical isomorphism of categories" is most
usefully exposed as this specified comparison functor together with a `Functor.IsEquivalence`
instance. Calling `Functor.asEquivalence` remains available to a consumer that really needs a
chosen inverse, but that choice-based package is not a second canonical data owner.

The project imports are public because their square, comparison, bilimit, and symmetric-model
APIs occur in exported declarations. `Mathlib.Tactic.CrossRefAttribute` is plain because it is used only to
elaborate the source tag; no tactic, diagnostic, or proof-only dependency is re-exported.
-/

namespace CategoricalPullback.CatCommSqOver

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable {X : Type (max u v)} [Category.{v} X]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- A categorical commutative square is a bilimit precisely when its canonical comparison
`Q.comparison : X ⥤ F ⊡ G` is an equivalence. The invertible square cell is already stored by
`CatCommSqOver`; this requires no `IsGroupoid` assumptions on the category objects. -/
theorem isBilimit_iff_comparisonIsEquivalence (Q : CatCommSqOver F G X) :
    Q.IsBilimit ↔ Q.comparison.IsEquivalence := sorry
/- Proof strategy: identify maps from a source square `R` to `Q` with lifts of
`R.comparison` through `Q.comparison`. If the comparison is an equivalence, transport the
canonical terminal lift. Conversely, use the terminal and walking-arrow source categories to
obtain essential surjectivity and full faithfulness. -/

/-- The canonical comparison of a `2`-fibre-product square is an equivalence. -/
theorem comparisonIsEquivalence
    (Q : CatCommSqOver F G X) [Q.IsBilimit] :
    Q.comparison.IsEquivalence := sorry
/- Proof strategy: apply the forward implication of
`isBilimit_iff_comparisonIsEquivalence` to the supplied bilimit instance. -/

end CategoricalPullback.CatCommSqOver

noncomputable section

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {S : Type (max u v)} [Category.{v} S]
variable {X : Type (max u v)} [Category.{v} X]
variable (G₁ : A ⥤ S) (G₂ : B ⥤ S)
variable (P : CatCommSqOver (G₁.prod G₂) (Functor.diag S) X)

namespace CategoricalPullback.CatCommSqOver.Symmetric

/- The source square and the direction of its structural natural isomorphism are

```
                              P.fst
             X ─────────────────────────────────▶ A × B
             │                                      │
       P.snd │                                      │ G₁.prod G₂
             ▼                                      ▼
             S ─────────────────────────────────▶ S × S
                         Functor.diag S
```

Thus `P.iso : P.fst ⋙ G₁.prod G₂ ≅ P.snd ⋙ Functor.diag S`. The comparison used below has
the source-faithful direction

```
       X ───────────────▶ (G₁.prod G₂) ⊡ Functor.diag S ───────────────▶ G₁ ⊡ G₂
            P.comparison                 CategoricalPullback.Symmetric.comparison G₁ G₂
```

This factorization is the reusable mathematical data. Its inverse is only determined up to
natural isomorphism, so a public choice of quasi-inverse would not be a more canonical owner. -/

/-- The canonical comparison attached to the symmetric presentation of a
`2`-fibre product. It first compares `P` with
`(G₁.prod G₂) ⊡ Functor.diag S`, then applies the canonical comparison with the ordinary
pullback `G₁ ⊡ G₂`. -/
def comparison : X ⥤ G₁ ⊡ G₂ :=
  P.comparison ⋙ CategoricalPullback.Symmetric.comparison G₁ G₂

namespace comparison

/-- The canonical comparison from any pseudo-pullback bilimit square over
`G₁.prod G₂` and `Functor.diag S` to the ordinary pullback `G₁ ⊡ G₂` is an equivalence.
When explicit equivalence data is required, mathlib provides
`(comparison G₁ G₂ P).asEquivalence`; its chosen inverse is deliberately not
declared as a second public owner. -/
@[stacks 02XE "symmetric 2-fibre-product comparison"]
theorem isEquivalence
    [P.IsBilimit] :
    (comparison G₁ G₂ P).IsEquivalence := sorry
/- Proof strategy: the first factor is an equivalence by
`CatCommSqOver.comparisonIsEquivalence`; the second is the symmetric-to-ordinary comparison
equivalence `CategoricalPullback.Symmetric.comparison.isEquivalence`. Apply mathlib's
composition instance for
`Functor.IsEquivalence`. -/

end comparison

end CategoricalPullback.CatCommSqOver.Symmetric

end

end CategoryTheory.Limits
