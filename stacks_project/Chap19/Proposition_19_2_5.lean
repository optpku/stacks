/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.OrdinalSmall
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {R : Type u} [Ring R]
variable (M : ModuleCat.{u} R) (α : Ordinal.{u})
variable (hM : Cardinal.mk (Submodule R M) < α.cof)

/- Proposition 19.2.5 (05NT): if `α.cof` is larger than the set of submodules of `M`, then
`M` is `α`-small with respect to injections, modeled canonically as monomorphisms in
`ModuleCat R`. -/
@[stacks 05NT] #check
  (ModuleCat.OrdinalSmall.monomorphisms_of_submodule_lt_cof M α hM :
    (MorphismProperty.monomorphisms (ModuleCat R)).IsOrdinalSmall M α)
