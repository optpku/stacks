/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Finite connected limits under equivalence

This leaf transports the aggregate existence properties across equivalences of categories. The
transport is deliberately exposed as named theorems rather than instances: choosing an
equivalence is data, not a canonical typeclass-search step.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace HasFiniteConnectedLimits

/-- Finite connected limits transport from the target of an equivalence functor to its source. -/
theorem ofEquivalence (E : C ⥤ D) [E.IsEquivalence] [HasFiniteConnectedLimits D] :
    HasFiniteConnectedLimits C := sorry

/-- Having finite connected limits is invariant under an equivalence of categories. -/
theorem iff_ofEquivalence (e : C ≌ D) :
    HasFiniteConnectedLimits C ↔ HasFiniteConnectedLimits D := sorry

end HasFiniteConnectedLimits

namespace HasFiniteConnectedColimits

/-- Finite connected colimits transport from the target of an equivalence functor to its source. -/
theorem ofEquivalence (E : C ⥤ D) [E.IsEquivalence] [HasFiniteConnectedColimits D] :
    HasFiniteConnectedColimits C := sorry

/-- Having finite connected colimits is invariant under an equivalence of categories. -/
theorem iff_ofEquivalence (e : C ≌ D) :
    HasFiniteConnectedColimits C ↔ HasFiniteConnectedColimits D := sorry

end HasFiniteConnectedColimits

end CategoryTheory.Limits
