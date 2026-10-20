/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Bounded Complex Inclusions

This leaf records the canonical finite-limit and finite-colimit preservation
properties of the inclusions of bounded-below, bounded-above, and bounded
cochain complexes. Keeping these as global instances avoids rebuilding them
locally whenever a short exact sequence of a bounded complex category is viewed
among all cochain complexes.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

namespace Plus

/-- Stacks 0159: the inclusion of bounded-below cochain complexes preserves
finite limits whenever they exist in the coefficient category. -/
@[stacks 0159]
instance inclusion_preservesFiniteLimits [HasFiniteLimits C] :
    PreservesFiniteLimits (ι C) := sorry

/-- Stacks 0159: the inclusion of bounded-below cochain complexes preserves
finite colimits whenever they exist in the coefficient category. -/
@[stacks 0159]
instance inclusion_preservesFiniteColimits [HasFiniteColimits C] :
    PreservesFiniteColimits (ι C) := sorry

end Plus

namespace Minus

/-- The inclusion of bounded-above cochain complexes preserves finite limits
whenever they exist in the coefficient category. -/
instance inclusion_preservesFiniteLimits [HasFiniteLimits C] :
    PreservesFiniteLimits (ι C) := sorry

/-- The inclusion of bounded-above cochain complexes preserves finite colimits
whenever they exist in the coefficient category. -/
instance inclusion_preservesFiniteColimits [HasFiniteColimits C] :
    PreservesFiniteColimits (ι C) := sorry

end Minus

namespace Bounded

/-- The inclusion of bounded cochain complexes preserves finite limits whenever
they exist in the coefficient category. -/
instance inclusion_preservesFiniteLimits [HasFiniteLimits C] :
    PreservesFiniteLimits (ι C) := sorry

/-- The inclusion of bounded cochain complexes preserves finite colimits
whenever they exist in the coefficient category. -/
instance inclusion_preservesFiniteColimits [HasFiniteColimits C] :
    PreservesFiniteColimits (ι C) := sorry

end Bounded

end CochainComplex
