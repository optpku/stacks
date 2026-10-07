module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import stacks_project.Chap61.Lemma_61_8_7_Cover
public import stacks_project.Chap61.Remark_61_5_4_Cardinality
public import stacks_project.Chap61.Remark_61_8_2_Cardinality

/-!
# Cardinality of the w-local ind-étale cover

If `κ` is an infinite cardinal at least as large as `#A`, then the cover
`Cover A` constructed in Lemma 61.8.7 has cardinality at most `κ`.
-/

@[expose] public section

universe u

open scoped Cardinal

namespace Algebra.WLocalIndEtale

/-- The w-local faithfully flat ind-étale cover `Cover A` has cardinality at most
`κ` whenever `κ` is infinite and `#A ≤ κ`. -/
theorem cardinalMk_cover_le (A : Type u) [CommRing A] {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) : #(Cover A) ≤ κ :=
  sorry

/-- Equivalent packaging: `#(Cover A) ≤ #A ⊔ ℵ₀`. -/
theorem cardinalMk_cover_le_max (A : Type u) [CommRing A] :
    #(Cover A) ≤ #A ⊔ ℵ₀ :=
  sorry

end Algebra.WLocalIndEtale
