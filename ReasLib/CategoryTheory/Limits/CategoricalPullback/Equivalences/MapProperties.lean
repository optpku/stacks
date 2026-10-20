module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map

/-!
# Property transfer for categorical-pullback maps

Instances transferring faithfulness, fullness, essential surjectivity, and equivalence along the
canonical map induced by a categorical cospan transformation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

namespace Limits.CategoricalPullback

/- Import decision: `Categorical.Basic` is public because every exported owner in this file is a
functor or equivalence between categorical pullbacks and exposes their projections and morphisms.
No chapter-local construction is needed in the public signatures. -/

section MapProperties

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]
variable {H : X ⥤ Z} {I : Y ⥤ Z} {F : A ⥤ C} {G : B ⥤ C}

/- The four declarations below are the property-transfer API for the canonical
`CategoricalPullback.map`. Mathlib has the analogous `Comma.faithful_map`, `Comma.full_map`,
`Comma.essSurj_map`, and `Comma.isEquivalenceMap`; categorical pullbacks use a separate
iso-comma model, so these instances are stated directly for that model. -/

namespace map

/-- Faithful functors on the two sides of a cospan transformation induce a faithful functor on
categorical pullbacks. -/
@[stacks 02XB "faithfulness of the induced 2-fibre-product functor"]
instance faithful (ψ : CatCospanTransform H I F G)
    [ψ.left.Faithful] [ψ.right.Faithful] :
    (map ψ).Faithful := sorry
/- Proof strategy: use `CategoricalPullback.hom_ext`; equality after `map ψ` gives equality of
the two projected components, which `ψ.left.map_injective` and `ψ.right.map_injective`
reflect. -/

/-- Full functors on the two sides of a cospan transformation induce a full functor on categorical
pullbacks when its base functor is faithful. -/
@[stacks 02XB "full faithfulness of the induced 2-fibre-product functor"]
instance full (ψ : CatCospanTransform H I F G)
    [ψ.left.Full] [ψ.right.Full] [ψ.base.Faithful] :
    (map ψ).Full := sorry
/- Proof strategy: lift the two components of a target morphism with `Functor.preimage`; applying
`ψ.base.map_injective` to the required compatibility equation reduces it to the target
compatibility equation, conjugated by the two invertible square cells. -/

/-- Essentially surjective functors on the two sides of a cospan transformation induce an
essentially surjective functor on categorical pullbacks when its base functor is fully faithful. -/
@[stacks 02XB "essential surjectivity of the induced 2-fibre-product functor"]
instance essSurj (ψ : CatCospanTransform H I F G)
    [ψ.left.EssSurj] [ψ.right.EssSurj] [ψ.base.Full] [ψ.base.Faithful] :
    (map ψ).EssSurj := sorry
/- Proof strategy: choose preimages of the two components using side essential surjectivity. The
target structural isomorphism and the square cells give an isomorphism between their images under
`ψ.base`; lift it with the fully faithful base functor, then use its faithfulness to prove that
the lifted inverse laws hold and form the required source pullback object. -/

/-- Fully faithful essentially surjective functors on the two sides of a cospan transformation
induce an equivalence on categorical pullbacks when its base functor is fully faithful.

The hypotheses are deliberately stated through the three property classes rather than through
`Functor.IsEquivalence`: this is the weakest reusable transfer statement, and an existing
equivalence supplies them automatically. -/
@[stacks 02XB "equivalence of the induced 2-fibre-product functor"]
instance isEquivalence (ψ : CatCospanTransform H I F G)
    [ψ.left.Full] [ψ.left.Faithful] [ψ.left.EssSurj]
    [ψ.right.Full] [ψ.right.Faithful] [ψ.right.EssSurj]
    [ψ.base.Full] [ψ.base.Faithful] :
    (map ψ).IsEquivalence := sorry
/- Proof strategy: assemble `Functor.IsEquivalence` from `map.faithful`, `map.full`, and
`map.essSurj`. -/

end map

end MapProperties

end Limits.CategoricalPullback

end CategoryTheory
