/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.8.6: if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, and `α` is an effective relative `r`-cycle on `X / S`, then
`Supp(α)` is closed in `X`. -/
@[stacks 0H5W] #check (AlgebraicGeometry.RelativeCycle.isClosed_support_of_isEffective :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r},
    IsRelative α → IsEffective α → IsClosed (Scheme.Hom.CyclesOnFibers.support α))

/- The support of a family in `z^{eff}(X/S, r)` is closed in `X`. -/
#check (AlgebraicGeometry.RelativeCycle.isClosed_support_of_mem_effective :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ} {α : f.FiberCycleFamily r},
    α ∈ effective f r → IsClosed (Scheme.Hom.CyclesOnFibers.support α))

end AlgebraicGeometry.RelativeCycle
