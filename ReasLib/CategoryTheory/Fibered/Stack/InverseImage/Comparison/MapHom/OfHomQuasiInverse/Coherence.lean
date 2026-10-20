/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.OfHomQuasiInverse

/-!
# Choice coherence for the Hom-quasi-inverse presentation

The specialized API lets inverse-image consumers change the chosen quasi-inverse without
unfolding the generic lift construction.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]

namespace StackOver.InverseImage.mapHom.ofHomQuasiInverse

variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}

/-- Changing the Hom quasi-inverse preserves the canonical comparison with postcomposition. -/
@[stacks 04WS "Hom-quasi-inverse comparison choice coherence"]
theorem choiceIso.comparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q q' : Functor.QuasiInverse (I.homFunctor I'.target)) :
    Functor.isoWhiskerRight (choiceIso I I' q q') (I.homFunctor I'.target) ≪≫
        comparisonIso I I' q' =
      comparisonIso I I' q := sorry

/-- The forward Hom-quasi-inverse choice triangle commutes at every stack morphism. -/
@[stacks 04WS "Hom-quasi-inverse choice forward component"]
theorem choiceIso.hom.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q q' : Functor.QuasiInverse (I.homFunctor I'.target))
    (F : S ⟶ S') :
    (I.homFunctor I'.target).map ((choiceIso I I' q q').hom.app F) ≫
        (comparisonIso I I' q').hom.app F =
      (comparisonIso I I' q).hom.app F := sorry

/-- The inverse Hom-quasi-inverse choice triangle commutes at every stack morphism. -/
@[stacks 04WS "Hom-quasi-inverse choice inverse component"]
theorem choiceIso.inv.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q q' : Functor.QuasiInverse (I.homFunctor I'.target))
    (F : S ⟶ S') :
    (comparisonIso I I' q').inv.app F ≫
        (I.homFunctor I'.target).map ((choiceIso I I' q q').inv.app F) =
      (comparisonIso I I' q).inv.app F := sorry

/-- The Hom-quasi-inverse choice comparison from a choice to itself is the identity. -/
@[simp, stacks 04WS "Hom-quasi-inverse choice reflexivity"]
theorem choiceIso.refl
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (I.homFunctor I'.target)) :
    choiceIso I I' q q = Iso.refl (mapHom.ofHomQuasiInverse I I' q) := sorry

/-- Reversing a Hom-quasi-inverse choice comparison exchanges its choices. -/
@[simp, stacks 04WS "Hom-quasi-inverse choice symmetry"]
theorem choiceIso.symm
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q q' : Functor.QuasiInverse (I.homFunctor I'.target)) :
    (choiceIso I I' q q').symm = choiceIso I I' q' q := sorry

/-- Hom-quasi-inverse choice comparisons compose transitively. -/
@[stacks 04WS "Hom-quasi-inverse choice transitivity"]
theorem choiceIso.trans
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q q' q'' : Functor.QuasiInverse (I.homFunctor I'.target)) :
    choiceIso I I' q q' ≪≫ choiceIso I I' q' q'' = choiceIso I I' q q'' := sorry

end StackOver.InverseImage.mapHom.ofHomQuasiInverse

end CategoryTheory
