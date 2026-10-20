/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Data.List.TFAE

/-!
# Criteria for finite limits and colimits

Finite limits and colimits can be recognized from their standard generating shapes. Named
pairwise equivalences complement the symmetric TFAE statements so callers do not depend on list
indices.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

namespace HasFiniteLimits

/-- Finite limits are equivalent to finite products together with equalizers. -/
theorem iff_hasFiniteProducts_and_equalizers :
    HasFiniteLimits C ↔ HasFiniteProducts C ∧ HasEqualizers C := sorry

/-- Finite limits are equivalent to a terminal object together with pullbacks. -/
theorem iff_hasTerminal_and_pullbacks :
    HasFiniteLimits C ↔ HasTerminal C ∧ HasPullbacks C := sorry

/-- Finite limits, finite products with equalizers, and a terminal object with pullbacks are
equivalent conditions. -/
@[stacks 002O "finite limit criteria"]
theorem tfae :
    [HasFiniteLimits C, HasFiniteProducts C ∧ HasEqualizers C,
      HasTerminal C ∧ HasPullbacks C].TFAE := sorry

end HasFiniteLimits

namespace HasFiniteColimits

/-- Finite colimits are equivalent to finite coproducts together with coequalizers. -/
theorem iff_hasFiniteCoproducts_and_coequalizers :
    HasFiniteColimits C ↔ HasFiniteCoproducts C ∧ HasCoequalizers C := sorry

/-- Finite colimits are equivalent to an initial object together with pushouts. -/
theorem iff_hasInitial_and_pushouts :
    HasFiniteColimits C ↔ HasInitial C ∧ HasPushouts C := sorry

/-- Finite colimits, finite coproducts with coequalizers, and an initial object with pushouts are
equivalent conditions. -/
@[stacks 002Q "finite colimit criteria"]
theorem tfae :
    [HasFiniteColimits C, HasFiniteCoproducts C ∧ HasCoequalizers C,
      HasInitial C ∧ HasPushouts C].TFAE := sorry

end HasFiniteColimits

end CategoryTheory.Limits
