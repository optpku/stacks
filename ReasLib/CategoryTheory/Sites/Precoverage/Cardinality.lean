module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Family
public import ReasLib.CategoryTheory.Sites.PrecoverageSite
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinally generated precoverages

This module records when every covering presieve is presented by a family whose index type is
small relative to a chosen cardinal.  It retains the chosen family data alongside the equivalent
cardinality formulation in terms of the raw presieve.
-/

@[expose] public section

open CategoryTheory

universe wκ w v u

namespace CategoryTheory

namespace Presieve

variable {C : Type u} [Category.{v} C]

/-- A cardinal bound on the raw arrows of a presieve is equivalent to a cardinal bound on a
chosen generating family, retaining its index type. -/
theorem hasGeneratingFamilyOfCardinalLT_iff
    {U : C} (R : Presieve U) (κ : Cardinal.{wκ}) :
    R.hasGeneratingFamilyOfCardinalLT κ ↔ HasCardinalLT R.uncurry κ := sorry

end Presieve

namespace Precoverage

variable {C : Type u} [Category.{v} C]

/-- Every covering presieve of `K` has raw arrow type of cardinality strictly below `κ`.  This is
the canonical cardinality condition on a precoverage and does not choose a presentation. -/
@[stacks 0GS0]
def hasCardinalLTCoveringPresieves (K : Precoverage C) (κ : Cardinal.{wκ}) : Prop :=
  ∀ ⦃U : C⦄ ⦃R : Presieve U⦄, R ∈ K U → HasCardinalLT R.uncurry κ

/-- Every covering presieve of `K` admits a generating family whose index type has cardinality
strictly below `κ`.  This is a presentation-dependent proposition, so it is an explicit
hypothesis rather than a typeclass. -/
def hasCardinalLTGeneratingFamilies (K : Precoverage C) (κ : Cardinal.{wκ}) : Prop :=
  ∀ ⦃U : C⦄ ⦃R : Presieve U⦄, R ∈ K U →
    R.hasGeneratingFamilyOfCardinalLT κ

/-- The generating-family cardinality condition is equivalent to the raw-presieve
cardinality condition. -/
theorem hasCardinalLTGeneratingFamilies_iff
    (K : Precoverage C) (κ : Cardinal.{wκ}) :
    K.hasCardinalLTGeneratingFamilies κ ↔ K.hasCardinalLTCoveringPresieves κ := sorry

end Precoverage

namespace Coverage

variable {C : Type u} [Category.{v} C]

/-- The canonical raw-presieve cardinality condition for a coverage, viewed through its
underlying precoverage. -/
abbrev hasCardinalLTCoveringPresieves (K : Coverage C) (κ : Cardinal.{wκ}) : Prop :=
  K.toPrecoverage.hasCardinalLTCoveringPresieves κ

/-- The cardinally small generating-family condition for a coverage, viewed through its
underlying precoverage. -/
abbrev hasCardinalLTGeneratingFamilies (K : Coverage C) (κ : Cardinal.{wκ}) : Prop :=
  K.toPrecoverage.hasCardinalLTGeneratingFamilies κ

end Coverage

end CategoryTheory

noncomputable section

open CategoryTheory
open scoped Cardinal

namespace CategoryTheory.Precoverage

/-- The precoverage of presieves whose uncurried support has cardinality at most `κ`. -/
def cardinalLE (C : Type u) [Category.{v} C] (κ : Cardinal.{wκ}) : Precoverage C where
  coverings X :=
    {R : Presieve X | Cardinal.lift.{wκ} #(R.uncurry) ≤ Cardinal.lift.{max u v} κ}

variable {C : Type u} [Category.{v} C]

/-- Membership in `cardinalLE C κ` is the lifted cardinality bound on the uncurried support. -/
theorem mem_cardinalLE_iff {X : C} {R : Presieve X} {κ : Cardinal.{wκ}} :
    R ∈ cardinalLE C κ X ↔
      Cardinal.lift.{wκ} #(R.uncurry) ≤ Cardinal.lift.{max u v} κ :=
  sorry

/-- An indexed family of arrows presents a `cardinalLE` covering when the index type is
bounded by `κ`. -/
theorem ofArrows_mem_cardinalLE {X : C} {ι : Type w} (Y : ι → C)
    (f : (i : ι) → Y i ⟶ X) {κ : Cardinal.{wκ}}
    (hι : Cardinal.lift.{wκ} #ι ≤ Cardinal.lift.{w} κ) :
    Presieve.ofArrows Y f ∈ cardinalLE C κ X :=
  sorry

/-- The cardinal truncation of covering presieves is monotone in the bound. -/
theorem cardinalLE_mono {κ κ' : Cardinal.{wκ}} (h : κ ≤ κ') :
    cardinalLE C κ ≤ cardinalLE C κ' :=
  sorry

/-- Singleton isomorphisms cover in `cardinalLE C κ` as soon as `1 ≤ κ`. -/
theorem hasIsos_cardinalLE {κ : Cardinal.{wκ}} (hκ : (1 : Cardinal.{wκ}) ≤ κ) :
    (cardinalLE C κ).HasIsos :=
  sorry

/-- Singleton isomorphisms cover in `cardinalLE C κ` as soon as `1 ≤ κ`. -/
instance instHasIsos_cardinalLE {κ : Cardinal.{wκ}} [hκ : Fact ((1 : Cardinal.{wκ}) ≤ κ)] :
    (cardinalLE C κ).HasIsos :=
  hasIsos_cardinalLE hκ.out

/-- Intersection of a precoverage with the cardinal truncation `cardinalLE C κ`. -/
def restrictCardinalLE (J : Precoverage C) (κ : Cardinal.{wκ}) : Precoverage C :=
  J ⊓ cardinalLE C κ

/-- Membership in `J.restrictCardinalLE κ` is `J`-covering together with the bound `≤ κ`. -/
theorem mem_restrictCardinalLE_iff {J : Precoverage C} {κ : Cardinal.{wκ}}
    {X : C} {R : Presieve X} :
    R ∈ J.restrictCardinalLE κ X ↔
      R ∈ J X ∧ Cardinal.lift.{wκ} #(R.uncurry) ≤ Cardinal.lift.{max u v} κ :=
  sorry

/-- Cardinal truncation of a precoverage is a sub-precoverage. -/
theorem restrictCardinalLE_le (J : Precoverage C) (κ : Cardinal.{wκ}) :
    J.restrictCardinalLE κ ≤ J :=
  sorry

/-- Every covering presieve of a cardinal truncation satisfies the bound `≤ κ`. -/
theorem restrictCardinalLE_hasCardinalLE (J : Precoverage C) (κ : Cardinal.{wκ})
    {X : C} {R : Presieve X} (hR : R ∈ J.restrictCardinalLE κ X) :
    Cardinal.lift.{wκ} #(R.uncurry) ≤ Cardinal.lift.{max u v} κ :=
  sorry

/-- An infinite-cardinal truncation of a site is a site. -/
theorem isSite_restrictCardinalLE {J : Precoverage C} [J.IsSite]
    {κ : Cardinal.{wκ}} (hκ : ℵ₀ ≤ κ) : (J.restrictCardinalLE κ).IsSite :=
  sorry

/-- An infinite-cardinal truncation of a site is a site. -/
instance instIsSite_restrictCardinalLE {J : Precoverage C} [J.IsSite]
    {κ : Cardinal.{wκ}} [hκ : Fact (ℵ₀ ≤ κ)] : (J.restrictCardinalLE κ).IsSite :=
  isSite_restrictCardinalLE hκ.out

end CategoryTheory.Precoverage
