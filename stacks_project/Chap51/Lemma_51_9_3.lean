/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Finiteness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/- Lemma 51.9.3: on a Noetherian scheme with a chosen dualizing complex, the locus where a
coherent `(S_k)` module has depth `k` and stalk-support dimension greater than `k` is finite. -/
@[stacks 0ECN] #check
  (@AlgebraicGeometry.Scheme.IsDualizingComplex.finite_setOf_depth_eq_and_lt_supportDim :
    {X : Scheme.{u}} → [IsNoetherian X] →
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} →
      Scheme.IsDualizingComplex ω → (F : X.Modules) → [F.IsCoherent] → (k : ℕ) →
      Scheme.Modules.satisfiesSerreConditionS F k →
    Set.Finite {x : X |
      Scheme.Modules.hasDepthAt F x k ∧
        (k : WithBot ℕ∞) <
          Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)})

end AlgebraicGeometry.Scheme.IsDualizingComplex
