module

public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Injective
public import ReasLib.CategoryTheory.Filtration.IntervalSplit.Computation
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered-Injective Interval Presentations

This module records the filtered-injective structure of the canonical interval-split model and
the classification of finite filtered-injective objects by such models.
-/

@[expose] public section

open CategoryTheory

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.IntervalSplit

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Local instance justification (instance diamond): Mathlib intentionally keeps this canonical
-- Abelian construction local because registering it globally interferes with unrelated
-- finite-(co)product instance search.
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every stage of an interval-split filtered object is injective when all its summands are
injective. -/
theorem Stage.injective (a b : ℤ) (J : Set.Icc a b → C)
    (hJ : ∀ i, Injective (J i)) (p : ℤ) :
    Injective ((filteredObject a b J).obj.stage p) := sorry

namespace FilteredInjective

/-- An interval-split filtered object is filtered injective when each of its summands is
injective, with the component hypothesis supplied explicitly. -/
theorem of_components (a b : ℤ) (J : Set.Icc a b → C)
    (hJ : ∀ i, Injective (J i)) :
    FilteredObject.IsFilteredInjective (filteredObject a b J).obj := sorry

end FilteredInjective

/-- The interval-split filtered object associated to an injective family is filtered injective. -/
instance filteredInjective (a b : ℤ) (J : Set.Icc a b → C)
    [∀ i, Injective (J i)] :
    FilteredObject.IsFilteredInjective (filteredObject a b J).obj := sorry

/-- A finite filtered object has an injective interval presentation if it is isomorphic to the
canonical interval-split object attached to a finite family of injective objects. -/
@[stacks 05TP "injective interval presentation predicate"]
def HasInjectivePresentation (I : FilteredObject.Finite.category C) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧ ∃ J : Set.Icc a b → C,
    (∀ i, Injective (J i)) ∧ Nonempty (I ≅ filteredObject a b J)

/-- Explicit data presenting a finite filtered object by an interval-split family of injectives.

The lower and upper bounds, the summand family, its injectivity certificates, and the comparison
isomorphism are all exposed as fields.  This is the reusable data owner; the older
`HasInjectivePresentation` predicate remains the proposition-level existence interface. -/
@[stacks 05TP "injective interval presentation data"]
structure InjectivePresentation (I : FilteredObject.Finite.category C) where
  /-- The lower endpoint of the interval. -/
  lower : ℤ
  /-- The upper endpoint of the interval. -/
  upper : ℤ
  /-- The interval endpoints are ordered. -/
  lower_le_upper : lower ≤ upper
  /-- The family of interval summands. -/
  family : Set.Icc lower upper → C
  /-- Every interval summand is injective. -/
  injective : ∀ i, Injective (family i)
  /-- The comparison with the canonical interval-split filtered model. -/
  iso : I ≅ filteredObject lower upper family

namespace InjectivePresentation

/-- The source-facing specification carried by an injective interval presentation. -/
@[stacks 05TP "injective interval presentation specification"]
abbrev Spec {I : FilteredObject.Finite.category C}
    (P : InjectivePresentation I) : Prop :=
  P.lower ≤ P.upper ∧
    (∀ i, Injective (P.family i)) ∧
      Nonempty (I ≅ filteredObject P.lower P.upper P.family)

/-- The canonical interval-split model carried by a presentation. -/
@[stacks 05TP "injective presentation model"]
noncomputable abbrev model {I : FilteredObject.Finite.category C}
    (P : InjectivePresentation I) :
    FilteredObject.Finite.category C :=
  filteredObject P.lower P.upper P.family

/-- Transport an injective interval presentation along an isomorphism of finite filtered objects.

The interval data are retained verbatim; only the comparison isomorphism is composed with the
transport isomorphism. -/
@[stacks 05TP "transport of injective interval presentations"]
def ofIso {I J : FilteredObject.Finite.category C} (e : I ≅ J)
    (P : InjectivePresentation J) : InjectivePresentation I where
  lower := P.lower
  upper := P.upper
  lower_le_upper := P.lower_le_upper
  family := P.family
  injective := P.injective
  iso := e ≪≫ P.iso

/-- An explicit presentation implies the proposition-level presentation predicate. -/
@[stacks 05TP]
theorem hasPresentation {I : FilteredObject.Finite.category C}
    (P : InjectivePresentation I) :
    HasInjectivePresentation I := sorry

/-- The underlying finite filtered object of an explicit presentation is filtered injective. -/
@[stacks 05TP]
theorem isFilteredInjective {I : FilteredObject.Finite.category C}
    (P : InjectivePresentation I) :
    FilteredObject.IsFilteredInjective I.obj := sorry

/-- Every explicit presentation satisfies its source-facing specification. -/
@[stacks 05TP "injective interval presentation specification"]
theorem spec {I : FilteredObject.Finite.category C}
    (P : InjectivePresentation I) : Spec P := sorry

end InjectivePresentation

namespace HasInjectivePresentation

/-- The proposition-level predicate is equivalent to nonempty explicit presentation data. -/
@[stacks 05TP]
theorem iff_nonempty (I : FilteredObject.Finite.category C) :
    HasInjectivePresentation I ↔ Nonempty (InjectivePresentation I) := sorry

/-- Choose explicit presentation data from a proof of the proposition-level predicate.

The choice is encapsulated behind this owner and its specification theorem, so downstream code
can use the named projections instead of inspecting an existential witness. -/
@[stacks 05TP "chosen injective interval presentation"]
noncomputable def choose {I : FilteredObject.Finite.category C}
    (hI : HasInjectivePresentation I) : InjectivePresentation I :=
  Classical.choice ((iff_nonempty I).mp hI)

/-- The chosen presentation has the explicit source-facing specification. -/
@[stacks 05TP "chosen injective interval presentation specification"]
theorem choose_spec {I : FilteredObject.Finite.category C}
    (hI : HasInjectivePresentation I) :
    InjectivePresentation.Spec (choose hI) := sorry

end HasInjectivePresentation

namespace FilteredInjective

/-- An explicit injective interval presentation supplies filtered-injectivity of its object. -/
@[stacks 05TP]
theorem ofPresentation {I : FilteredObject.Finite.category C}
    (P : InjectivePresentation I) :
    FilteredObject.IsFilteredInjective I.obj := sorry

/-- An injective interval presentation equips a finite filtered object with the canonical
filtered-injective structure. -/
theorem of_hasPresentation (I : FilteredObject.Finite.category C)
    (hI : HasInjectivePresentation I) :
    FilteredObject.IsFilteredInjective I.obj := sorry

/-- Every finite filtered-injective object admits an injective interval presentation. -/
theorem hasPresentation (I : FilteredObject.Finite.category C)
    [FilteredObject.IsFilteredInjective I.obj] :
    HasInjectivePresentation I := sorry

/-- Lemma 13.26.2 (`05TP`): finite filtered-injective objects are exactly the finite filtered
objects admitting an injective interval presentation. -/
@[stacks 05TP]
theorem iff_hasPresentation (I : FilteredObject.Finite.category C) :
    FilteredObject.IsFilteredInjective I.obj ↔ HasInjectivePresentation I := sorry

end FilteredInjective

namespace InjectivePresentation

/-- Explicit injective interval presentation data are available for every finite
filtered-injective object. -/
@[stacks 05TP "existence of injective interval presentation data"]
theorem nonempty (I : FilteredObject.Finite.category C)
    [FilteredObject.IsFilteredInjective I.obj] :
    Nonempty (InjectivePresentation I) := sorry

end InjectivePresentation

end CategoryTheory.FilteredObject.IntervalSplit
