module

public import Mathlib.SetTheory.Cardinal.Basic
public import stacks_project.Chap61.«61_5_2_5_WLocalization»

/-!
# Cardinality of w-localization

If `κ` is an infinite cardinal at least as large as `#A`, then each finite-stage
algebra `stage A E`, the poset `Finset A`, and the w-localization
`wLocalization A` all have cardinality at most `κ`.
-/

@[expose] public section

universe u

open scoped Cardinal

namespace Algebra.WLocalHull

/-- The poset of finite subsets of `A` has cardinality at most `κ` whenever
`κ` is infinite and `#A ≤ κ`. -/
theorem cardinalMk_finset_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) : #(Finset A) ≤ κ :=
  sorry

/-- Each finite-stage algebra `stage A E` has cardinality at most `κ` whenever
`κ` is infinite and `#A ≤ κ`. -/
theorem cardinalMk_stage_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (E : Finset A) : #(stage A E) ≤ κ :=
  sorry

/-- The w-localization `wLocalization A` has cardinality at most `κ` whenever
`κ` is infinite and `#A ≤ κ`. -/
theorem cardinalMk_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) : #(wLocalization A) ≤ κ :=
  sorry

/-- Equivalent packaging: `#(wLocalization A) ≤ max ℵ₀ #A`. -/
theorem cardinalMk_le_max (A : Type u) [CommRing A] :
    #(wLocalization A) ≤ max ℵ₀ #A :=
  sorry

end Algebra.WLocalHull
