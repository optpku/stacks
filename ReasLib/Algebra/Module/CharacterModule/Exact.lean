/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.LinearAlgebra.LeftExact
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exactness of additive character duality
-/

universe u v w

namespace CharacterModule

variable {A : Type u} {B : Type v} {C : Type w}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- At the underlying additive level, dualizing an exact pair whose second map
is surjective gives an exact pair in the opposite direction. -/
@[stacks 01DA "exactness of additive character duality"]
theorem exact_dual (f : A →+ B) (g : B →+ C)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact
      (CharacterModule.dual g.toIntLinearMap)
      (CharacterModule.dual f.toIntLinearMap) := sorry
/- Proof strategy: apply `LinearMap.exact_lcomp_of_exact_of_surjective` over
`ℤ` with target `AddCircle (1 : ℚ)`, then identify `LinearMap.lcomp` with
`CharacterModule.dual`. -/

end CharacterModule
