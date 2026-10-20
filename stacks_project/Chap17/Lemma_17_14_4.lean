/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Rank
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 17.14.4 (01C9): a locally free module sheaf over a ringed space with nontrivial
structure-sheaf stalks admits a locally constant rank function recording every local free-basis
cardinality. -/
@[stacks 01C9]
#check fun {X : RingedSpace.{u}} (F : X.Modules) [F.IsLocallyFree]
    (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x)) ↦
  (SheafOfModules.IsLocallyFree.exists_rankFunction F h𝒪 :
    ∃ rank : X → ℕ∞, SheafOfModules.IsRankFunction F rank)

#check @SheafOfModules.IsRankFunction
#check @SheafOfModules.isRankFunction_iff
#check @SheafOfModules.IsRankFunction.isLocallyConstant
#check @SheafOfModules.IsRankFunction.eq_card
#check @SheafOfModules.IsLocallyFree.rankAtStalk_isRankFunction
#check @SheafOfModules.IsLocallyFree.rankAtStalk_isLocallyConstant
#check @SheafOfModules.rankAtStalk
#check @SheafOfModules.rankAtStalk_eq_of_iso
#check @SheafOfModules.rankAtStalk_eq_card_of_iso
#check @SheafOfModules.IsFiniteLocallyFreeOfRank.rankAtStalk_eq
#check @SheafOfModules.IsRankFunction.eq
#check @SheafOfModules.IsLocallyFree.existsUnique_rankFunction
