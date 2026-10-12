/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08NU

# Kan fibrations of simplicial sets

This file supplies the canonical base-change-stability instance for Kan fibrations that is not
already exposed by the model-category API. Limit-shaped closure instances live in a dedicated
leaf module.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet.modelCategoryQuillen

namespace J

namespace rlp

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- Definition 14.31.1 (08NU): lifting against `J` is equivalent to lifting against every
positive-dimensional horn inclusion. -/
@[stacks 08NU "right lifting against J is horn lifting"]
theorem iff_horn :
    J.rlp f ↔ ∀ (n : ℕ) (i : Fin (n + 2)),
      HasLiftingProperty (horn (n + 1) i).ι f := sorry

end rlp

end J

namespace fibration

/-- Lemma 14.31.2 (08NV), at the morphism-property level: Kan fibrations of simplicial sets are
stable under base change. -/
@[stacks 08NV "base-change stability of Kan fibrations"]
instance baseChange :
    (fibrations SSet.{u}).IsStableUnderBaseChange := sorry

end fibration

end SSet.modelCategoryQuillen
