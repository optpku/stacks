/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Valuation.ValuationRing
import StacksCheckRecall

@[expose] public section

/-!
# The value group of a valuation ring

@stack 00ID
-/

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

-- Local declaration justification (source-local notation): `Γ` is only a compact spelling of the
-- value-group units used in the source statement; the reusable owner remains `ValueGroup`.
local notation "Γ" => (ValuationRing.ValueGroup A (FractionRing A))ˣ

/- Lemma 10.50.12: if `A` is a valuation ring with fraction field `K`, then
`Γ = Kˣ / Aˣ`, ordered by the image of `A \ {0}`, is a totally ordered abelian group. Mathlib's
canonical with-zero owner is `ValuationRing.ValueGroup A (FractionRing A)`; its units form `Γ`. -/
@[stacks 00ID "commutative group structure"]
#check (inferInstance : CommGroup Γ)

@[stacks 00ID "linear order"]
#check (inferInstance : LinearOrder Γ)

@[stacks 00ID "ordered monoid compatibility"]
#check (inferInstance : IsOrderedMonoid Γ)

end
