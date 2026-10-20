/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective.Split

/-!
# Categorical Retracts of Finite Projective Modules

This leaf translates the linear split API to categorical retracts in
`ModuleCat`.
-/

@[expose] public section

universe u v

namespace Module.FiniteProjective

variable {R : Type u} [Ring R]

/-- Tag `00JH`: a categorical retract of a finite projective module is finite projective.
For `r : CategoryTheory.Retract M P`, the underlying maps satisfy
`r.r.hom.comp r.i.hom = LinearMap.id` on `M`. -/
@[stacks 00JH "finite projective modules are closed under categorical retracts"]
theorem of_retract {M P : ModuleCat.{v} R}
    (hP : Module.FiniteProjective R P) (r : CategoryTheory.Retract M P) :
    Module.FiniteProjective R M := by
  apply hP.of_split r.i.hom r.r.hom
  ext x
  exact DFunLike.congr_fun (congr_arg ModuleCat.Hom.hom r.retract) x

end Module.FiniteProjective
