/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap35.«35_4_11_1_TensorHom»
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom.SplitCoequalizer
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

universe u

/- Remark 35.4.11: tensoring the arguments of a split coequalizer of character
modules on the right by any module again gives a split coequalizer. -/
@[stacks 08WS] #check
  (CharacterModule.TensorHom.mapIsSplitCoequalizer :
    (R : Type u) → [CommRing R] → {M N P : ModuleCat.{u} R} →
      (Q : ModuleCat.{u} R) →
      {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N} →
      {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P} →
      IsSplitCoequalizer f g π →
        IsSplitCoequalizer
          (CharacterModule.TensorHom.rightMap R Q f)
          (CharacterModule.TensorHom.rightMap R Q g)
          (CharacterModule.TensorHom.rightMap R Q π))
