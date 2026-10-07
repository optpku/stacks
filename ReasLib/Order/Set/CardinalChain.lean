module

public import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cardinal bounds for well-ordered chains of sets

A strictly monotone or antitone well-ordered family of subsets sharing one element
cannot have larger cardinality than its ambient type.  This order-theoretic owner is
independent of the subobject applications that motivated it.
-/

@[expose] public section

universe u

namespace Set.CardinalChain

/-- A well-ordered strictly increasing family of subsets with a common element cannot be
indexed by a type larger than the ambient type. -/
@[stacks 0E8N "increasing set-chain bound"]
theorem noStrictMono {ι T : Type u} [LinearOrder ι] [WellFoundedLT ι] {z : T}
    (h : Cardinal.mk T < Cardinal.mk ι) :
    ¬ ∃ S : ι → Set T, StrictMono S ∧ ∀ i, z ∈ S i := sorry

/-- A well-ordered strictly decreasing family of subsets with a common element cannot be
indexed by a type larger than the ambient type. -/
@[stacks 0E8N "decreasing set-chain bound"]
theorem noStrictAnti {ι T : Type u} [LinearOrder ι] [WellFoundedLT ι] {z : T}
    (h : Cardinal.mk T < Cardinal.mk ι) :
    ¬ ∃ S : ι → Set T, StrictAnti S ∧ ∀ i, z ∈ S i := sorry

end Set.CardinalChain
