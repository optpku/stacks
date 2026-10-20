/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# Finite limits of formal coproducts

This leaf packages the terminal-object and pullback constructions supplied by
mathlib into the finite-limit interface used by fixed-target families.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Formal coproducts have finite limits when their component category has a terminal object
and pullbacks. -/
instance instHasFiniteLimits [HasTerminal C] [HasPullbacks C] :
    HasFiniteLimits (FormalCoproduct.{w} C) := sorry

end FormalCoproduct
end Limits

end CategoryTheory
