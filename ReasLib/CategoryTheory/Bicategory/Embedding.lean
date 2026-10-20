/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Functor.Embedding

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u

/-
API hierarchy for equality-sensitive bicategorical embeddings:

* A `StrictPseudofunctor B C` supplies the general presentation data, and its `IsEmbedding`
  property says that this presentation identifies `B` with a sub-`2`-category of `C`.
* `FullSubbicategory` and `LocallyInducedBicategory` are canonical constructors for the locally
  full special cases: they select objects and possibly `1`-morphisms while retaining all ambient
  `2`-morphisms between the selected `1`-morphisms.
* `Functor.IsEmbedding` is the equality-sensitive `Cat` convention: injective on objects and
  faithful, with no fullness requirement.
* `StrictPseudofunctor.IsEmbedding` iterates that convention homwise, adding strict
  injectivity on objects and `1`-morphisms and faithfulness on `2`-morphisms.
* `Pseudofunctor.IsLocallyFullyFaithful` instead asks for homwise fullness and faithfulness but
  no equality-level injectivity on objects or `1`-morphisms.
* `Pseudofunctor.IsLocallyEquivalence` strengthens the local invariant condition by requiring
  each hom functor to be an equivalence.

Consequently there is intentionally no conversion between strict embeddings and either local
predicate. Full-subbicategory inclusions have separate instances because they happen to satisfy
both kinds of condition.

Import decision: `FullSubbicategory` is public because this file supplies embedding instances for
its canonical `ι` and `ιOfLE` inclusions.
-/

namespace StrictPseudofunctor

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- Definition 4.29.2 (Stacks 02X7): a strict pseudofunctor is an equality-sensitive embedding
when it is injective on objects and, for every `X Y : B`, the functor

```
                         F.mapFunctor X Y
       B(X, Y) ─────────────────────────────▶ C(F.obj X, F.obj Y)
```

is an ordinary categorical embedding. The same condition gives an equality-level subbicategory
presentation without strictness assumptions, so the reusable owner is stated for bicategories.

The hom-functor condition simultaneously says that `1`-morphisms are mapped injectively and
that `2`-morphisms are mapped faithfully. Strict pseudofunctoriality supplies the source's
closure under identities and horizontal composition.

This condition is deliberately orthogonal to `Pseudofunctor.IsLocallyFullyFaithful`: local full
faithfulness requires fullness on `2`-morphisms but no strict injectivity on `1`-morphisms.
`Pseudofunctor.IsLocallyEquivalence` additionally requires homwise essential surjectivity;
neither invariant local condition supplies equality-level injectivity on objects. -/
@[stacks 02X7 "sub-2-categories as strict pseudofunctor embeddings"]
class IsEmbedding (F : StrictPseudofunctor B C) : Prop where
  /-- Distinct source objects remain distinct in the target bicategory. -/
  obj_injective : Function.Injective F.obj
  /-- Every induced functor on a hom category is an embedding. -/
  mapFunctor_isEmbedding (X Y : B) : (F.mapFunctor X Y).IsEmbedding

attribute [instance] IsEmbedding.mapFunctor_isEmbedding

/-- A strict pseudofunctor is an embedding exactly when it is injective on objects and each
induced hom functor is a categorical embedding. -/
theorem isEmbedding_iff (F : StrictPseudofunctor B C) :
    F.IsEmbedding ↔ Function.Injective F.obj ∧
      ∀ X Y : B, (F.mapFunctor X Y).IsEmbedding := sorry
/- Proof strategy: extract the two class fields forward and use them to construct
`StrictPseudofunctor.IsEmbedding` backward. -/

/-- A strict pseudofunctor embedding is injective on `1`-morphisms. -/
theorem IsEmbedding.map_injective (F : StrictPseudofunctor B C) [F.IsEmbedding]
    {X Y : B} : Function.Injective (fun f : X ⟶ Y ↦ F.map f) := sorry
/- Proof strategy: apply `Functor.IsEmbedding.obj_injective` to the categorical embedding
`F.mapFunctor X Y`; its object action is definitionally `F.map`. -/

/-- A strict pseudofunctor embedding is injective on `2`-morphisms. -/
theorem IsEmbedding.map₂_injective (F : StrictPseudofunctor B C) [F.IsEmbedding]
    {X Y : B} {f g : X ⟶ Y} :
    Function.Injective (fun η : f ⟶ g ↦ F.map₂ η) := sorry
/- Proof strategy: use `(F.mapFunctor X Y).map_injective`; its `Faithful` instance is inherited
from `IsEmbedding.mapFunctor_isEmbedding X Y`, and its morphism action is `F.map₂`. -/

end StrictPseudofunctor

namespace ObjectProperty.FullSubbicategory

universe w₁ v₁ u₁

variable {D : Type u₁} [Bicategory.{w₁, v₁} D]
variable {P Q : ObjectProperty D}

/-- The canonical inclusion of a full subbicategory is an equality-level embedding. -/
instance ιIsEmbedding (P : ObjectProperty D) : (ι P).IsEmbedding := sorry
/- Proof strategy: subtype coercion is injective on objects; each hom functor is faithful, and
its object map merely removes the `InducedBicategory.Hom` wrapper. -/

/-- An inclusion induced by `P ≤ Q` is an equality-level embedding. -/
instance ιOfLEIsEmbedding (h : P ≤ Q) : (ιOfLE h).IsEmbedding := sorry
/- Proof strategy: equality of target subtype objects implies equality of their ambient values;
the hom functors again only remove and rebuild induced-hom wrappers. -/

end ObjectProperty.FullSubbicategory

end CategoryTheory
