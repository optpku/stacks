/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Injective.Baer.Transfinite
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Adjunction
public import ReasLib.CategoryTheory.Action.ModuleCat.Cofree.Adjunction
public import ReasLib.CategoryTheory.Action.Zero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial injective embeddings for algebraic linear actions

The cofree adjunction transfers the canonical Baer embeddings from `ModuleCat R` to the category
of algebraic `R`-linear `G`-actions. Keeping this transfer separate leaves the cofree construction
usable without importing transfinite iteration.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.Action.ModuleCat

noncomputable section

variable (R : Type u) (G : Type v) [Ring R] [Monoid G]

/-- Algebraic `R`-linear `G`-actions have functorial injective embeddings. -/
@[stacks 04JF "algebraic action category"]
noncomputable instance hasFunctorialInjectives :
    HasFunctorialInjectives (Action (ModuleCat.{max u v} R) G) :=
  HasFunctorialInjectives.of_rightAdjointWith
    (_root_.ModuleCat.Baer.hasFunctorialInjectives.{v, u} R) (Cofree.adjunction R G)
    (fun X hX ↦ Action.isZero_of_forget_obj_isZero X hX)

end

end CategoryTheory.Action.ModuleCat
