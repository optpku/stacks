module

public import ReasLib.Algebra.WLocalHull.Cardinality

/-!
# Cardinality of w-localization

If `κ` is an infinite cardinal at least as large as `#A`, then each finite-stage
algebra `stage A E` and the w-localization
`wLocalization A` all have cardinality at most `κ`.
-/

@[expose] public section

universe u

open scoped Cardinal

#check (Algebra.WLocalHull.cardinalMk_stage_le :
  ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}},
    ℵ₀ ≤ κ → #A ≤ κ → ∀ (E : Finset A), #(Algebra.WLocalHull.stage A E) ≤ κ)

#check (Algebra.WLocalHull.cardinalMk_le :
  ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}},
    ℵ₀ ≤ κ → #A ≤ κ → #(Algebra.WLocalHull.wLocalization A) ≤ κ)

#check (Algebra.WLocalHull.cardinalMk_le_max :
  ∀ (A : Type u) [CommRing A],
    #(Algebra.WLocalHull.wLocalization A) ≤ max ℵ₀ #A)
