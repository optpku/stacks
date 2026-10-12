/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.SetTheory.Cardinal.Basic
public import stacks_project.Chap07.Definition_7_6_2_Site

@[expose] public section

universe u v w wκ

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
