/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Coskeleton.Projection
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits Opposite
open scoped Simplicial

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (k n : ℕ) [SimplicialObject.Truncated.HasCoskeletons C n] (T : C)

/- Equation 25.7.3.1 (0B16). The simplicial object Hom(C[k], T) has degree-q object
the product of T indexed by maps [k] → [q]. The displayed map is the degree-(n+1)
component of the canonical unit into coskₙ skₙ Hom(C[k], T).
The source uses this construction in SR(C, X), which has finite limits. -/
@[stacks 0B16 "canonical costandard-power coskeleton-unit map"] #check
  (SimplicialObject.CostandardPower.unitComponent k n T :
    (SimplicialObject.CostandardPower.object k T).obj (op ⦋n + 1⦌) ⟶
      ((SimplicialObject.Truncated.cosk n).obj
        ((SimplicialObject.truncation n).obj
          (SimplicialObject.CostandardPower.object k T))).obj (op ⦋n + 1⦌))

end CategoryTheory
