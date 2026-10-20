/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RelativeCycle.Equalizer

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.12: if `S` is locally Noetherian and `f : X ⟶ S` is locally of finite
type, then for relative `r`-cycles `α, β` the fibrewise equalizer
`E = eqLocus α β` is a closed subset of `S`. -/
@[stacks 0H5C] #check (AlgebraicGeometry.RelativeCycle.isClosed_eqLocus :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    {α β : f.FiberCycleFamily r},
    IsRelative α → IsRelative β → IsClosed (AlgebraicGeometry.RelativeCycle.eqLocus α β))

end AlgebraicGeometry.RelativeCycle
