module

-- Import decisions:
-- * `Groupoids.Basic` is public because `toGroupoids` exposes the bundled groupoid-fibred owner.
-- * `DiscreteFibration.Fibers` is public because the object property exposes
--   `IsDiscreteFibration` and its groupoid-fibred refinement.
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
import Mathlib.Tactic.CrossRefAttribute

/-!
# The bicategory of categories fibred in sets

The full subbicategory of based categories whose projection is a discrete fibration,
together with its object constructors and canonical forgetful views.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

/-
The suitable owner is the direct full sub-`2`-category of `BasedCategory C` selected by
`Functor.IsDiscreteFibration X.p`. Fullness retains the canonical based functors and based
natural transformations over `C`, while the object predicate gives the groupoid-fibred refinement
through `toGroupoids`. Strict discreteness is deliberately not declared invariant under arbitrary
equivalence over `C`: the equivalence-invariant essentially-discrete layer is
`FiberedCategoryOver.Setoids`.
-/

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- The object property on `BasedCategory C` selecting projections fibred in sets. -/
abbrev isFiberedInSets (C : Type u) [Category.{v} C] :
    ObjectProperty (BasedCategory.{vS, w} C) :=
  fun X ↦ Functor.IsDiscreteFibration X.p

/-- Being fibred in sets implies being fibred in groupoids, as an inequality of the canonical
object properties on `BasedCategory C`. This is the object-level map underlying the forgetful
strict pseudofunctor below. -/
theorem isFiberedInSets.le_isFiberedInGroupoids :
    (isFiberedInSets C : ObjectProperty (BasedCategory.{vS, w} C)) ≤
      (isFiberedInGroupoids C : ObjectProperty (BasedCategory.{vS, w} C)) := sorry
/- Proof strategy: for each based category selected by `BasedCategory.isFiberedInSets`, apply
`Functor.IsDiscreteFibration.toInGroupoids` to its projection. -/

/-
There is deliberately no `ObjectProperty.IsClosedUnderEquivalences` instance here. Already over
the terminal base, the terminal category is equivalent to a thin groupoid with two distinct but
uniquely isomorphic objects; only the former is strictly discrete. Thus an equivalence of based
categories can preserve the associated set-valued presheaf without preserving
`Functor.IsDiscreteFibration` on the nose.
-/

end BasedCategory

set_option linter.checkUnivs false in
/-- The `2`-category of categories fibred in sets over `C`
consists of based categories over `C` whose projection is a discrete fibration. The two
total-category universes are deliberately independent although the carrier sort records only
their maximum. -/
@[stacks 04S8 "(1) categories fibred in sets over a base"]
abbrev FiberedCategoryOver.Sets (C : Type u) [Category.{v} C] :=
  ((BasedCategory.isFiberedInSets C :
    ObjectProperty (BasedCategory.{vS, w} C))).FullSubbicategory

namespace FiberedCategoryOver.Sets

variable (C) in
/-- The canonical strict inclusion into the ambient `2`-category of based categories. It is the
single structured facade for forgetting objects, `1`-morphisms, and `2`-morphisms to their
based-category representations. -/
abbrev toBased : StrictPseudofunctor
    (FiberedCategoryOver.Sets C) (BasedCategory.{vS, w} C) :=
  ObjectProperty.FullSubbicategory.ι _

variable (C) in
/-- Forget discreteness from categories fibred in sets. Since both owners are full
subbicategories of the same `BasedCategory C`, this strict pseudofunctor canonically acts on
objects, `1`-morphisms, and `2`-morphisms.

The source and target in the result type determine both object properties and all universe
parameters; `BasedCategory.isFiberedInSets.le_isFiberedInGroupoids` is the canonical object-level
forgetful map. -/
def toGroupoids : StrictPseudofunctor
    (FiberedCategoryOver.Sets C) (FiberedCategoryOver.Groupoids C) :=
  FullSubbicategory.ιOfLE BasedCategory.isFiberedInSets.le_isFiberedInGroupoids

/-- Build a bundled category fibred in sets over `C` from a functor to `C`. -/
def ofFunctor
    {S : Type w} [Category.{vS} S] (p : S ⥤ C) [h : Functor.IsDiscreteFibration p] :
    FiberedCategoryOver.Sets C :=
  ⟨BasedCategory.ofFunctor p, h⟩

/- Axiom audit: the total category and projection of `ofFunctor p` are explicitly those of
`BasedCategory.ofFunctor p`; its owner-membership field is the supplied discrete-fibration
instance. -/

/-- The underlying based category over `C`. -/
abbrev toBasedCategory (X : FiberedCategoryOver.Sets C) : BasedCategory.{vS, w} C :=
  X.1

/-- The total category of a bundled category fibred in sets over `C`. -/
abbrev total (X : FiberedCategoryOver.Sets C) :=
  X.toBasedCategory.obj

/-- The projection functor of a bundled category fibred in sets over `C`. -/
abbrev p (X : FiberedCategoryOver.Sets C) :=
  X.toBasedCategory.p

/-- The underlying based category of `ofFunctor p` is the direct based-category owner for `p`. -/
@[simp]
theorem ofFunctor.toBasedCategory {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [Functor.IsDiscreteFibration p] :
    (ofFunctor p).toBasedCategory = BasedCategory.ofFunctor p := sorry

/-- The total category of `ofFunctor p` is the source category of `p`. -/
@[simp]
theorem ofFunctor.total {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [Functor.IsDiscreteFibration p] : (ofFunctor p).total = S := sorry

/-- The canonical projection of `ofFunctor p` is the supplied functor `p`. -/
@[simp]
theorem ofFunctor.p {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [Functor.IsDiscreteFibration p] : (ofFunctor p).p = p := sorry
/- Proof strategy: unfold `ofFunctor`, `FiberedCategoryOver.Sets.p`, and
`BasedCategory.ofFunctor`; the stored projection is definitionally `p`. -/

/-- Canonical coercion to the direct ambient based-category API. -/
instance coeBasedCategory : CoeOut (FiberedCategoryOver.Sets C) (BasedCategory.{vS, w} C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in sets is fibred in sets. This named
instance exposes the owner property to downstream fiber and cartesian-lift inference. -/
instance projectionInSets (X : FiberedCategoryOver.Sets C) :
    Functor.IsDiscreteFibration X.p := X.property

/-- Categories fibred in sets form a `(2,1)`-category. This owner-level instance is available
before the stronger local discreteness result `homIsDiscrete` in
`Fibered.InSets.LocalDiscreteness` and records the immediate consequence of forgetting to
categories fibred in groupoids. -/
instance locallyGroupoid : IsLocallyGroupoid (FiberedCategoryOver.Sets C) := sorry
/- Proof strategy: for each pair `X Y`, obtain groupoidality of the ambient based-functor hom
from `BasedFunctor.homGroupoid` and the groupoid-fibred structure of `Y.p`, then transport it
through `Bicategory.InducedBicategory.homGroupoid`. -/

end FiberedCategoryOver.Sets

end CategoryTheory
