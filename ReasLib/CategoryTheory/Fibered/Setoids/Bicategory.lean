module

-- Import decisions:
-- * `Bicategory.Equivalence` is public because the repleteness instance exposes
--   `ObjectProperty.IsClosedUnderEquivalences`.
-- * `Groupoids.Basic` is public because `toGroupoids` exposes its owner.
-- * `InSetoids` is public because it supplies the intrinsic projection predicate.
public import ReasLib.CategoryTheory.Bicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InSetoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# The bicategory of categories fibred in setoids

The replete full subbicategory of based categories whose projections are fibred in setoids.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

/-
The root owner is the full subbicategory of `BasedCategory C` selected by
`Functor.IsFibered.InSetoids X.p`, not a nested subtype of groupoid-fibred categories. Its
inherited `1`-morphisms are based functors over `C`; thin setoid fibres make each hom-category
thin, while the groupoid part makes it locally groupoidal.
-/

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- The object property on `BasedCategory C` selecting projections fibred in setoids. -/
abbrev isFiberedInSetoids (C : Type u) [Category.{v} C] :
    ObjectProperty (BasedCategory.{vS, w} C) :=
  fun X ↦ Functor.IsFibered.InSetoids X.p

/-- Being fibred in setoids implies being fibred in groupoids as an inequality of the canonical
object properties on `BasedCategory C`. -/
theorem isFiberedInSetoids.le_isFiberedInGroupoids :
    (isFiberedInSetoids C : ObjectProperty (BasedCategory.{vS, w} C)) ≤
      (isFiberedInGroupoids C : ObjectProperty (BasedCategory.{vS, w} C)) := sorry
/- Proof strategy: apply `Functor.IsFibered.InSetoids.toInGroupoids` to each projection. -/

/-- Being fibred in setoids is invariant under equivalence in the fixed bicategory
`BasedCategory C`. -/
theorem inSetoids_iff_of_equivalence
    {X Y : BasedCategory.{vS, w} C} (e : X ≌ Y) :
    Functor.IsFibered.InSetoids X.p ↔ Functor.IsFibered.InSetoids Y.p := sorry
/- Proof strategy: transport the groupoid-fibration component along the based equivalence and
transport faithfulness in both directions through its quasi-inverse. -/

/-- Being fibred in setoids is invariant under equivalence over the fixed base, so the selected
full subbicategory is replete. -/
instance isFiberedInSetoids.isClosedUnderEquivalences (C : Type u) [Category.{v} C] :
    (isFiberedInSetoids C).IsClosedUnderEquivalences := sorry
/- Proof strategy: apply `inSetoids_iff_of_equivalence` in the forward direction. -/

end BasedCategory

set_option linter.checkUnivs false in
/-- Definition 4.39.3 (Stacks 02Y1): the `2`-category of categories fibred in setoids over `C` consists of based categories whose projection
is fibred in setoids. The independent object and hom universes of the total categories are
retained even though the carrier sort sees only their maximum. -/
@[stacks 02Y1 "(1) categories fibred in setoids over a base"]
abbrev FiberedCategoryOver.Setoids (C : Type u) [Category.{v} C] :=
  ((BasedCategory.isFiberedInSetoids C : ObjectProperty (BasedCategory.{vS, w} C))).FullSubbicategory

namespace FiberedCategoryOver.Setoids

variable (C) in
/-- The canonical strict inclusion into the ambient `2`-category of based categories. It is the
single structured facade for forgetting objects, `1`-morphisms, and `2`-morphisms to their
based-category representations. -/
abbrev toBased : StrictPseudofunctor
    (FiberedCategoryOver.Setoids C) (BasedCategory.{vS, w} C) :=
  ObjectProperty.FullSubbicategory.ι _

variable (C) in
/-- Forget thinness from categories fibred in setoids. Since both owners are full
subbicategories of the same `BasedCategory C`, this strict pseudofunctor canonically acts on
objects, `1`-morphisms, and `2`-morphisms. -/
def toGroupoids : StrictPseudofunctor
    (FiberedCategoryOver.Setoids C) (FiberedCategoryOver.Groupoids C) :=
  FullSubbicategory.ιOfLE BasedCategory.isFiberedInSetoids.le_isFiberedInGroupoids

variable (C) in
/-- Forget the setoid-fibre refinement while retaining the underlying fibred category. This is
the canonical composite of forgetting thinness and then forgetting the groupoid-fibre
refinement. -/
@[stacks 02Y1 "forget setoid fibres to a fibred category"]
def toFibered : StrictPseudofunctor
    (FiberedCategoryOver.Setoids C) (FiberedCategoryOver C) :=
  (toGroupoids C).comp (FiberedCategoryOver.Groupoids.toFibered C)

/- Axiom audit: `toFibered` introduces no new data choice. Its non-Prop object, morphism, and
`2`-morphism actions are inherited from the two canonical forgetful strict pseudofunctors;
their `sorryAx` dependencies are confined to Prop-valued membership, hom-property, and
coherence fields. -/

/-- Build a bundled category fibred in setoids over `C` from a functor to `C`. -/
def ofFunctor
    {S : Type w} [Category.{vS} S] (p : S ⥤ C) [h : Functor.IsFibered.InSetoids p] :
    FiberedCategoryOver.Setoids C :=
  ⟨BasedCategory.ofFunctor p, h⟩

/- Axiom audit: the total category and projection of `ofFunctor p` are explicitly those of
`BasedCategory.ofFunctor p`; its owner-membership field is the supplied setoid-fibration
instance. -/

/-- The underlying based category over `C`. -/
abbrev toBasedCategory (X : FiberedCategoryOver.Setoids C) : BasedCategory.{vS, w} C :=
  X.1

/-- The total category of a bundled category fibred in setoids over `C`. -/
abbrev total (X : FiberedCategoryOver.Setoids C) :=
  X.toBasedCategory.obj

/-- The projection functor of a bundled category fibred in setoids over `C`. -/
abbrev p (X : FiberedCategoryOver.Setoids C) :=
  X.toBasedCategory.p

/-- The canonical projection of `ofFunctor p` is the supplied functor `p`. -/
@[simp]
theorem ofFunctor.p {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [Functor.IsFibered.InSetoids p] : (ofFunctor p).p = p := sorry
/- Proof strategy: unfold `ofFunctor`, `FiberedCategoryOver.Setoids.p`, and
`BasedCategory.ofFunctor`; the stored projection is definitionally `p`. -/

/-- Canonical coercion to the direct ambient based-category API. -/
instance coeBasedCategory : CoeOut (FiberedCategoryOver.Setoids C) (BasedCategory.{vS, w} C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in setoids is fibred in setoids. -/
instance projectionInSetoids (X : FiberedCategoryOver.Setoids C) :
    Functor.IsFibered.InSetoids X.p := X.property

/-- Every hom-category of categories fibred in setoids is thin. -/
@[stacks 02Y1 "setoid-fibred Hom categories are thin"]
instance homIsThin (X Y : FiberedCategoryOver.Setoids C) : Quiver.IsThin (X ⟶ Y) := sorry
/- Proof strategy: each vertical based natural-transformation component is identified by
faithfulness of the target projection. -/

/-- Categories fibred in setoids form a `(2,1)`-category. -/
@[stacks 02Y1 "categories fibred in setoids are locally groupoidal"]
instance locallyGroupoid : IsLocallyGroupoid (FiberedCategoryOver.Setoids C) := sorry
/- Proof strategy: use the groupoid-fibred structure of the target projection in each ambient
based-functor hom category. -/

end FiberedCategoryOver.Setoids

end CategoryTheory
