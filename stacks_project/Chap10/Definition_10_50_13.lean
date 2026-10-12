/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.50.13

@stack 00IE
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

/- Definition 10.50.13: for a valuation ring `A`, the value group is the ordered abelian group
`Γ = Kˣ / Aˣ`. In mathlib, this group is represented by the unit group of the canonical owner
object `ValuationRing.ValueGroup A (FractionRing A)`. -/
@[stacks 00IE]
#check (ValuationRing.ValueGroup A (FractionRing A))ˣ

end

/- Companion recall: the valuation associated to a valuation ring is the canonical valuation
`ValuationRing.valuation A (FractionRing A)` on its fraction field; its codomain is the with-zero
version of the value group from Definition 10.50.13, and restricting this map to
`A \ {0}` or to `(FractionRing A)ˣ` gives the textbook maps `v : A - \{0\} → Γ` and
`v : K^* → Γ`. -/
@[stacks 00IE "valuation attached to a valuation ring"]
#check @ValuationRing.valuation

/- Companion recall: adjoining `0` to the ordered abelian group from Definition 10.50.13 recovers
the canonical with-zero value group used by `ValuationRing.valuation`. -/
@[stacks 00IE "with-zero value group"]
#check @OrderMonoidIso.withZeroUnits

/- Companion recall: the further textbook condition that the value group be infinite cyclic is
formalized in mathlib by the standard predicate `IsDiscreteValuationRing A`. The corresponding
normalization of the associated with-zero value group by `ℤᵐ⁰` belongs to the separate
rank-one-discrete valuation API, not to the present definition of the value group itself. -/
@[stacks 00IE "discrete valuation companion"]
#check @IsDiscreteValuationRing

/- Companion recall: once `A` is a discrete valuation ring, the associated valuation on its
fraction field is canonically rank-one discrete. This is the bridge from the present value-group
definition to the `ℤᵐ⁰` normalization API. -/
@[stacks 00IE "rank-one discrete valuation bridge"]
#check @IsDiscreteValuationRing.isRankOneDiscrete
