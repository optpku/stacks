module

-- Import decisions:
-- * `Fibered.CategoryOver.Bicategory` is the public owner of the ambient bicategory.
-- * `Fibered.BasedCategory.InGroupoids` owns the generic based-category object property and its
--   equivalence-invariance API.
-- * `Fibered.InGroupoids.Cartesian` owns automatic strong-cartesianness preservation into a
--   groupoid-fibred target.
-- * `FullSubbicategory.Lift.Construction` is public because `toFibered` is the property-implication
--   inclusion `FullSubbicategory.ιOfLE` followed by the locally induced lift.
-- * mathlib's `Bicategory.LocallyGroupoid` is public because `locallyGroupoid` exposes its
--   canonical `(2,1)`-categorical property directly.
-- * Deferred proof dependencies are intentionally omitted at the statement stage: prose proof
--   strategies do not contribute declaration dependencies.
public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# The bicategory of categories fibred in groupoids

The canonical full subbicategory of based categories whose projections are fibred in groupoids,
together with its object constructors and forgetful views.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open BasedCategory
open scoped Bicategory

/-
Mathlib supplies `Bicategory.InducedBicategory` for changing an object carrier; the project's
`LocallyInducedBicategory` adds the separate local hom restriction. `FiberedCategoryOver C`
therefore restricts the objects of `BasedCategory C` to fibred projections and its `1`-morphisms
to strongly-cartesian-preserving based functors. For projections fibred in groupoids, every based
functor automatically has that preservation property. Hence the canonical owner here is the
object-only full subbicategory of `BasedCategory C`, induced by
`Bicategory.InducedBicategory`. Building it over `FiberedCategoryOver C` would retain a redundant
object and hom wrapper even though the extra local condition carries no data in this case.

The short `abbrev`s below are retained only for recurring reducible views: the object property and
full-subbicategory owner; the object projections `toBasedCategory`, `total`, and `p`; and the
canonical forgetful pseudofunctor `toBased`. All constructors of objects and pseudofunctors remain
ordinary `def`s.
-/

namespace FiberedCategoryOver
/-- Categories fibred in groupoids over `C` form the full induced
`2`-category of `BasedCategory C` cut out by `BasedCategory.isFiberedInGroupoids C`;
the canonical owner supplies all ambient `1`- and `2`-morphisms without another local wrapper.

The two total-category universes remain independent even though this carrier sort sees only their
maximum, exactly as for mathlib's `BasedCategory`. -/
@[stacks 02XS "(1) categories fibred in groupoids over a base"]
abbrev Groupoids (C : Type u) [Category.{v} C] :=
  ((BasedCategory.isFiberedInGroupoids C :
    ObjectProperty (BasedCategory.{vS, w} C))).FullSubbicategory

end FiberedCategoryOver

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- Build a bundled category fibred in groupoids over `C` from a functor to `C`. -/
def ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [h : Functor.IsFibered.InGroupoids p] :
    FiberedCategoryOver.Groupoids C :=
  ⟨BasedCategory.ofFunctor p, h⟩

/- Axiom audit: the total category and projection are explicitly those of
`BasedCategory.ofFunctor p`; the owner-membership field is the supplied groupoid-fibration
instance. -/

/-- The underlying based category over `C`. -/
abbrev toBasedCategory (X : FiberedCategoryOver.Groupoids C) : BasedCategory.{vS, w} C :=
  X.1

/-- The total category of a bundled category fibred in groupoids over `C`. -/
abbrev total (X : FiberedCategoryOver.Groupoids C) :=
  X.toBasedCategory.obj

/-- The projection functor of a bundled category fibred in groupoids over `C`. -/
abbrev p (X : FiberedCategoryOver.Groupoids C) :=
  X.toBasedCategory.p

/-- The canonical projection of `ofFunctor p` is the supplied functor `p`. -/
@[simp]
theorem ofFunctor.p {S : Type w} [Category.{vS} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p] : (ofFunctor p).p = p := sorry
/- Proof strategy: unfold `ofFunctor`, `FiberedCategoryOver.Groupoids.p`, and
`BasedCategory.ofFunctor`; the stored projection is definitionally `p`. -/

/-- The projection of a bundled category fibred in groupoids is fibred in groupoids. This is
exactly the property field of an object of the owner full subbicategory after unfolding the direct
based-category projection. -/
instance projectionInGroupoids (X : FiberedCategoryOver.Groupoids C) :
    Functor.IsFibered.InGroupoids X.p := X.property

/-- Categories fibred in groupoids form a `(2,1)`-category: every vertical based natural
transformation is invertible. This named owner instance is intentional because the object map of
`InducedBicategory` cannot be reconstructed from its carrier synonym by typeclass search alone.

Proof strategy: for each `X` and `Y`, obtain groupoidality of the ambient based-functor hom from
`BasedFunctor.homGroupoid` and `Y.property`, then transport it through
`Bicategory.InducedBicategory.homGroupoid`. -/
@[stacks 0040 "locally groupoidal bicategory of groupoid-fibred categories"]
instance locallyGroupoid : IsLocallyGroupoid (FiberedCategoryOver.Groupoids C) := sorry

/-- Canonical coercion to the direct ambient based-category API. -/
instance coeBasedCategory : CoeOut (FiberedCategoryOver.Groupoids C) (BasedCategory.{vS, w} C) where
  coe X := X.toBasedCategory

variable (C) in
/-- The canonical strict inclusion into the ambient `2`-category of based categories. It is the
single owner for forgetting objects, `1`-morphisms, and `2`-morphisms to their based-category
representations. -/
@[stacks 0040 "forget groupoid-fibred categories to based categories"]
abbrev toBased : StrictPseudofunctor
    (FiberedCategoryOver.Groupoids C) (BasedCategory.{vS, w} C) :=
  ObjectProperty.FullSubbicategory.ι _

variable (C) in
/-- Forget the groupoid-fibre condition while retaining the underlying fibred category.
The square of forgetful pseudofunctors is

```text
 FiberedCategoryOver.Groupoids C ────────────── toFibered ─────────────▶ FiberedCategoryOver C
                 │                                                               │
         toBased │                                                               │ FiberedCategoryOver.toBased
                 ▼                                                               ▼
          BasedCategory C ─────────────────────── 𝟭 ─────────────────────▶ BasedCategory C
```

The two vertical maps are `toBased` and `FiberedCategoryOver.toBased`.

The object implication forgets only the `IsFibered.InGroupoids` refinement. On `1`-morphisms,
`BasedFunctor.PreservesStronglyCartesian.ofTargetInGroupoids` supplies the hom
property that is automatic in the groupoid-fibred target; `2`-morphisms are unchanged.
The generic locally-induced lift is applied to the canonical inclusion between the two object
properties and owns all strict pseudofunctor coherence. -/
@[stacks 0040 "forget groupoid-fibred categories to fibred categories"]
def toFibered : StrictPseudofunctor
    (FiberedCategoryOver.Groupoids C) (FiberedCategoryOver C) :=
  LocallyInducedBicategory.lift
    (FullSubbicategory.ιOfLE
      (fun (_ : BasedCategory.{vS, w} C)
        (h : Functor.IsFibered.InGroupoids _) ↦ h.toIsFibered))
    (fun F ↦
      BasedFunctor.PreservesStronglyCartesian.ofTargetInGroupoids F.hom)

/- Axiom audit: `#print axioms` reports `sorryAx` for `toFibered` only through the
Prop-valued object-membership witness in `FullSubbicategory.ιOfLE`, the
hom-property witness, and strict-pseudofunctor coherence fields. Its non-Prop
`obj`/`map`/`map₂` data are inherited from the canonical inclusion and remain the corresponding
ambient based category, based functor, and based natural transformation; no semantic datum is
supplied by `sorry`. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
