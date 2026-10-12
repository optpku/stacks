/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Finite nonempty limits under equivalence

This leaf transports the aggregate existence properties across equivalences of categories. The
transport is deliberately exposed as named theorems rather than instances: choosing an
equivalence is data, not a canonical typeclass-search step.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace HasFiniteNonemptyLimits

/-- Finite nonempty limits transport from the target of an equivalence functor to its source. -/
theorem ofEquivalence (E : C ⥤ D) [E.IsEquivalence] [HasFiniteNonemptyLimits D] :
    HasFiniteNonemptyLimits C := sorry

/-- Having finite nonempty limits is invariant under an equivalence of categories. -/
theorem iff_ofEquivalence (e : C ≌ D) :
    HasFiniteNonemptyLimits C ↔ HasFiniteNonemptyLimits D := sorry

end HasFiniteNonemptyLimits

namespace HasFiniteNonemptyColimits

/-- Finite nonempty colimits transport from the target of an equivalence functor to its source. -/
theorem ofEquivalence (E : C ⥤ D) [E.IsEquivalence] [HasFiniteNonemptyColimits D] :
    HasFiniteNonemptyColimits C := sorry

/-- Having finite nonempty colimits is invariant under an equivalence of categories. -/
theorem iff_ofEquivalence (e : C ≌ D) :
    HasFiniteNonemptyColimits C ↔ HasFiniteNonemptyColimits D := sorry

end HasFiniteNonemptyColimits

end CategoryTheory.Limits
