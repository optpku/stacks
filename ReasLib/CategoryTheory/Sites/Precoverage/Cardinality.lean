/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

private theorem hasCardinalLT_uncurry_ofArrows
    {U : C} {ι : Type w} (Y : ι → C) (f : (i : ι) → Y i ⟶ U)
    {κ : Cardinal.{wκ}} (hι : HasCardinalLT ι κ) :
    HasCardinalLT (Presieve.ofArrows Y f).uncurry κ := by
  refine hι.of_surjective
    (fun i ↦ ⟨⟨Y i, f i⟩, Presieve.ofArrows.mk i⟩) ?_
  rintro ⟨⟨Z, g⟩, ⟨i⟩⟩
  exact ⟨i, rfl⟩

/-- A cardinal bound on the raw arrows of a presieve is equivalent to a cardinal bound on a
chosen generating family, retaining its index type. -/
theorem hasGeneratingFamilyOfCardinalLT_iff
    {U : C} (R : Presieve U) (κ : Cardinal.{wκ}) :
    R.hasGeneratingFamilyOfCardinalLT κ ↔ HasCardinalLT R.uncurry κ := by
  constructor
  · rintro ⟨g, hg⟩
    rw [← g.generates]
    exact hasCardinalLT_uncurry_ofArrows _ _ hg
  · intro hR
    refine ⟨
      { family := ⟨R.uncurry, fun i ↦ CategoryTheory.Over.mk i.1.2⟩
        generates := ?_ }, hR⟩
    refine le_antisymm ?_ ?_
    · rintro _ _ ⟨i⟩
      exact i.2
    · intro Y f hf
      exact Presieve.ofArrows.mk (⟨⟨Y, f⟩, hf⟩ : R.uncurry)

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
    K.hasCardinalLTGeneratingFamilies κ ↔ K.hasCardinalLTCoveringPresieves κ := by
  constructor
  · intro h U R hR
    exact (R.hasGeneratingFamilyOfCardinalLT_iff κ).mp (h hR)
  · intro h U R hR
    exact (R.hasGeneratingFamilyOfCardinalLT_iff κ).mpr (h hR)

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
  Iff.rfl

private theorem mem_cardinalLE_iff_hasCardinalLT
    {X : C} {R : Presieve X} {κ : Cardinal.{wκ}} :
    R ∈ cardinalLE C κ X ↔ HasCardinalLT R.uncurry (Order.succ κ) := by
  simp [mem_cardinalLE_iff, HasCardinalLT, Cardinal.lift_succ, Order.lt_succ_iff]

/-- An indexed family of arrows presents a `cardinalLE` covering when the index type is
bounded by `κ`. -/
theorem ofArrows_mem_cardinalLE {X : C} {ι : Type w} (Y : ι → C)
    (f : (i : ι) → Y i ⟶ X) {κ : Cardinal.{wκ}}
    (hι : Cardinal.lift.{wκ} #ι ≤ Cardinal.lift.{w} κ) :
    Presieve.ofArrows Y f ∈ cardinalLE C κ X :=
  mem_cardinalLE_iff_hasCardinalLT.mpr
    (Presieve.hasCardinalLT_uncurry_ofArrows Y f (by
      simpa [HasCardinalLT, Cardinal.lift_succ, Order.lt_succ_iff] using hι))

/-- The cardinal truncation of covering presieves is monotone in the bound. -/
theorem cardinalLE_mono {κ κ' : Cardinal.{wκ}} (h : κ ≤ κ') :
    cardinalLE C κ ≤ cardinalLE C κ' :=
  by
    intro X R hR
    exact mem_cardinalLE_iff.mpr
      ((mem_cardinalLE_iff.mp hR).trans (Cardinal.lift_le.mpr h))

/-- Singleton isomorphisms cover in `cardinalLE C κ` as soon as `1 ≤ κ`. -/
theorem hasIsos_cardinalLE {κ : Cardinal.{wκ}} (hκ : (1 : Cardinal.{wκ}) ≤ κ) :
    (cardinalLE C κ).HasIsos :=
  ⟨fun f _ ↦ by simpa [mem_cardinalLE_iff] using hκ⟩

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
  Iff.rfl

/-- Cardinal truncation of a precoverage is a sub-precoverage. -/
theorem restrictCardinalLE_le (J : Precoverage C) (κ : Cardinal.{wκ}) :
    J.restrictCardinalLE κ ≤ J :=
  inf_le_left

/-- Every covering presieve of a cardinal truncation satisfies the bound `≤ κ`. -/
theorem restrictCardinalLE_hasCardinalLE (J : Precoverage C) (κ : Cardinal.{wκ})
    {X : C} {R : Presieve X} (hR : R ∈ J.restrictCardinalLE κ X) :
    Cardinal.lift.{wκ} #(R.uncurry) ≤ Cardinal.lift.{max u v} κ :=
  hR.2

/-- An infinite-cardinal truncation of a site is a site. -/
theorem isSite_restrictCardinalLE {J : Precoverage C} [J.IsSite]
    {κ : Cardinal.{wκ}} (hκ : ℵ₀ ≤ κ) : (J.restrictCardinalLE κ).IsSite :=
  by
    letI : (cardinalLE C κ).HasIsos :=
      hasIsos_cardinalLE (Cardinal.one_le_aleph0.trans hκ)
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    refine
      { toHasIsos := (inferInstance : (J ⊓ cardinalLE C κ).HasIsos)
        toHasPullbacks := ⟨fun f hR ↦ J.hasPullbacks_of_mem f hR.1⟩
        toIsStableUnderBind := ⟨?_⟩
        toIsStableUnderPullbackArrows := ⟨?_⟩ }
    · intro U R hR S hS
      refine ⟨IsStableUnderBind.bind_mem hR.1 S (fun {_} f hf ↦ (hS f hf).1), ?_⟩
      apply mem_cardinalLE_iff_hasCardinalLT.mpr
      have h := hasCardinalLT_sigma
        (fun i : R.uncurry ↦ (S i.1.2 i.2).uncurry) (Order.succ κ)
        (mem_cardinalLE_iff_hasCardinalLT.mp hR.2)
        (fun i ↦ mem_cardinalLE_iff_hasCardinalLT.mp (hS i.1.2 i.2).2)
      refine h.of_surjective
        (fun ij ↦ ⟨⟨ij.2.1.1, ij.2.1.2 ≫ ij.1.1.2⟩,
          Presieve.bind_comp _ ij.1.2 ij.2.2⟩) ?_
      rintro ⟨⟨Z, h⟩, hh⟩
      obtain ⟨Y, g, f, hf, hg, hcomp⟩ := hh
      refine ⟨⟨⟨⟨Y, f⟩, hf⟩, ⟨⟨Z, g⟩, hg⟩⟩, ?_⟩
      exact Subtype.ext (congrArg (Sigma.mk Z) hcomp)
    · intro U V f R _ hR
      refine ⟨IsStableUnderPullbackArrows.pullbackArrows_mem f hR.1, ?_⟩
      apply mem_cardinalLE_iff_hasCardinalLT.mpr
      have h := mem_cardinalLE_iff_hasCardinalLT.mp hR.2
      haveI (i : R.uncurry) : Limits.HasPullback i.1.2 f := R.hasPullback f i.2
      refine h.of_surjective
        (fun i ↦ ⟨⟨Limits.pullback i.1.2 f, Limits.pullback.snd i.1.2 f⟩,
          Presieve.pullbackArrows.mk _ _ i.2⟩) ?_
      rintro ⟨⟨Z, g⟩, ⟨Y, h, hh⟩⟩
      exact ⟨⟨⟨Y, h⟩, hh⟩, rfl⟩

/-- An infinite-cardinal truncation of a site is a site. -/
instance instIsSite_restrictCardinalLE {J : Precoverage C} [J.IsSite]
    {κ : Cardinal.{wκ}} [hκ : Fact (ℵ₀ ≤ κ)] : (J.restrictCardinalLE κ).IsSite :=
  isSite_restrictCardinalLE hκ.out

end CategoryTheory.Precoverage
