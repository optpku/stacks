/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.Naturality
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.HomPresheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Strictification
import StacksCheckRecall

@[expose] public section

/-!
# Strictification and Hom-presheaf invariance

The strict-presheaf model and Hom-presheaf invariance are both shared owners.  The neutral
`CartesianBasedFunctor` interface allows the source and target total categories to live in
independent universes.  The `FiberedCategoryOver` interface remains the fixed-owner specialization
with identity and composition algebra.
-/

namespace CategoryTheory

/- Remark 8.2.4: every category fibred in groupoids has an equivalent strict
`Grpd`-valued presheaf model. -/
@[stacks 02ZA "(1) strict groupoid-valued presheaf model"]
#check @Functor.IsFibered.InGroupoids.Strictification.existsPresheafModel

/- Invariant companion: inside a fixed owner universe, strictification yields an actual
bicategorical equivalence to a split category fibred in groupoids. -/
#check @FiberedCategoryOver.Groupoids.Strictification.existsSplitModel

/- Neutral construction: a cartesian based functor induces a map between the lifted canonical
Hom-presheaves even when the two total categories live in different universes. -/
#check @CartesianBasedFunctor.HomPresheaf.Chosen.map

/- Its pointwise formula is expressed by conjugating the fiberwise map with the canonical
reindexing comparisons. -/
#check @CartesianBasedFunctor.HomPresheaf.Chosen.map.app.apply

/- Remark 8.2.4: an equivalence over the base makes the neutral Hom-presheaf map an isomorphism.
The equivalence proof can be passed directly to `CartesianBasedFunctor.ofIsEquivalence`; no local
instance is required. -/
@[stacks 02ZA "(2) Hom-presheaf invariance under equivalence"]
#check @CartesianBasedFunctor.HomPresheaf.Explicit.map.isIso_of_isEquivalence
#check @CartesianBasedFunctor.ofIsEquivalence

/- Fixed-owner specialization: a morphism of bundled fibred categories induces the same canonical
Hom-presheaf comparison. -/
#check @FiberedCategoryOver.Hom.presheafHomMap.isIso_of_isEquivalence

/- The canonical instance form lets ordinary consumers obtain the same fact by typeclass
search, while the identity and composition laws expose the functorial algebra. -/
#check @FiberedCategoryOver.Hom.presheafHomMap.isIso
#check @FiberedCategoryOver.Hom.presheafHomMap.id
#check @FiberedCategoryOver.Hom.presheafHomMap.comp

end CategoryTheory
