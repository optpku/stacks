module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.RingTheory.Localization.Cardinality
public import ReasLib.Algebra.WLocalIndEtale.Cover
public import ReasLib.Algebra.WLocalHull.Cardinality
public import ReasLib.Algebra.IndEtaleEnvelope.Cardinality

/-!
# Cardinality of w-local ind-étale covers

The concrete w-local faithfully flat ind-étale cover of a commutative ring has
cardinality bounded by any infinite cardinal bounding the original ring.
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

/-- The cardinality of the w-local faithfully flat ind-étale cover of a ring is
bounded by the maximum of its cardinality and the countably infinite cardinal. -/
theorem cardinalMk_cover_le_max (A : Type u) [CommRing A] :
    #(Cover A) ≤ #A ⊔ ℵ₀ :=
  sorry

end Algebra.WLocalIndEtale
