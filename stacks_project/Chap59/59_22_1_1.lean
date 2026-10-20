/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Sheaf.Coproducts
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {C : Type u} [Category.{u} C] [HasInitial C]
variable {J : GrothendieckTopology C}
variable {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
/- 59.22.1.1: sections of a sheaf over a disjoint coproduct are the product of
the sections over the coproduct summands. -/
@[stacks 03XC] #check
  (CategoryTheory.Presieve.isIso_sectionsToProduct_of_isSheaf :
    ∀ {C : Type u} [Category.{u} C] [HasInitial C]
      {J : GrothendieckTopology C}
      {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
      {I : C} {α : Type u} {X : α → C},
      IsInitial I →
      (c : Cofan X) →
      IsColimit c →
      [(Presieve.ofArrows X c.inj).HasPairwisePullbacks] →
      [∀ i, Mono (c.inj i)] →
      Presheaf.IsSheaf J F →
      Sieve.generate (Presieve.ofArrows X c.inj) ∈ J c.pt →
      Sieve.generate (⊥ : Presieve I) ∈ J I →
      Pairwise (fun i j ↦
        IsPullback (initial.to (X i)) (initial.to (X j)) (c.inj i) (c.inj j)) →
      IsIso (Pi.lift (fun i ↦ F.map (c.inj i).op)))
