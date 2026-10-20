module

public import ReasLib.Algebra.WLocalHull.Cardinality
import StacksCheckRecall

@[expose] public section

universe u

open scoped Cardinal

/- Remark 61.5.4: if `A` is a ring and `κ` is an infinite cardinal with `#A ≤ κ`,
then `#(wLocalization A) ≤ κ`. Namely each `stage A E` has cardinality at most
`κ` and `#(Finset A) ≤ κ` as well, using `κ * κ = κ`. -/
@[stacks 0976] #check (Algebra.WLocalHull.cardinalMk_le :
  ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}},
    ℵ₀ ≤ κ → #A ≤ κ → #(Algebra.WLocalHull.wLocalization A) ≤ κ)
