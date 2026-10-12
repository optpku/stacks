/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.ChaoticPower
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

/- Lemma 60.18.4 -/
@[stacks 07JM] #check
  (CategoryTheory.Sheaf.ChaoticPower.totalCohomology_isomorphic_positivePowerComplex :
    ∀ {C : Type u} [Category.{v} C] (X : C)
      (hX : ∀ Y : C, Nonempty (Y ⟶ X)) [HasBinaryProducts C]
      (F : Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})
      [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}]
      [HasGlobalSectionsFunctor (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}]
      [HasInjectiveResolutions (Sheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{w})],
      IsIsomorphic
        (((Sheaf.Γ (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}).rightDerivedToHomotopyCategory ⋙
          ComplexShape.embeddingUpNat.extendHomotopyFunctor AddCommGrpCat.{w} ⋙
          DerivedCategory.Qh).obj F)
        (DerivedCategory.Q.obj
          ((CategoryTheory.Sheaf.ChaoticPower.positivePowerComplex X F).extend
            ComplexShape.embeddingUpNat)))
