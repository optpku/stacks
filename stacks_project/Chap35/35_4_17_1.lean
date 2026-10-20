/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import stacks_project.Chap35.Lemma_35_4_16_SplitEqualizer
public import stacks_project.Chap35.Lemma_35_4_17_CharacterModule
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (D : ModuleCat.DescentData (algebraMap R S))

/- 35.4.17.1: applying character duality to the descent fork gives the displayed
cofork from the two character-dual tensor-cube maps to the character module of `D`. -/
@[stacks 08X2] #check
  (CategoryTheory.Limits.Fork.mapOp
    (Fork.ofι (ModuleCat.DescentData.SplitEqualizer.source D)
      (ModuleCat.DescentData.SplitEqualizer.condition D))
    CharacterModule.addCommGrpFunctor :
    Cofork
      (CharacterModule.addCommGrpFunctor.map
        (ModuleCat.DescentData.SplitEqualizer.upper D).op)
      (CharacterModule.addCommGrpFunctor.map
        (ModuleCat.DescentData.SplitEqualizer.lower D).op))

#check
  (CategoryTheory.Limits.Fork.mapOp_pt
    (Fork.ofι (ModuleCat.DescentData.SplitEqualizer.source D)
      (ModuleCat.DescentData.SplitEqualizer.condition D))
    CharacterModule.addCommGrpFunctor :
    (CategoryTheory.Limits.Fork.mapOp
      (Fork.ofι (ModuleCat.DescentData.SplitEqualizer.source D)
        (ModuleCat.DescentData.SplitEqualizer.condition D))
      CharacterModule.addCommGrpFunctor).pt =
        CharacterModule.addCommGrpFunctor.obj
          (Opposite.op (AddCommGrpCat.of
            (ModuleCat.DescentData.SplitEqualizer.component D))))

#check
  (CategoryTheory.Limits.Fork.mapOp_π
    (Fork.ofι (ModuleCat.DescentData.SplitEqualizer.source D)
      (ModuleCat.DescentData.SplitEqualizer.condition D))
    CharacterModule.addCommGrpFunctor :
    (CategoryTheory.Limits.Fork.mapOp
      (Fork.ofι (ModuleCat.DescentData.SplitEqualizer.source D)
        (ModuleCat.DescentData.SplitEqualizer.condition D))
      CharacterModule.addCommGrpFunctor).π =
        CharacterModule.addCommGrpFunctor.map
          (ModuleCat.DescentData.SplitEqualizer.source D).op)
