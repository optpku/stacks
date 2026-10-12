/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.EqualizerSheafCondition
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w)
variable {B : C} {I : Type t} [Small.{w} I] (X : I → C) (π : (i : I) → X i ⟶ B)
variable [(Presieve.ofArrows X π).HasPairwisePullbacks]

/- 7.7.1.1: the canonical restriction diagram, whose limiting property is the sheaf condition. -/
@[stacks 00VN] #check
  (CategoryTheory.Equalizer.Presieve.Arrows.fork P X π :
    Fork (CategoryTheory.Equalizer.Presieve.Arrows.firstMap P X π)
      (CategoryTheory.Equalizer.Presieve.Arrows.secondMap P X π))

#check (CategoryTheory.Equalizer.Presieve.Arrows.forkMap P X π :
  P.obj (op B) ⟶ CategoryTheory.Equalizer.Presieve.Arrows.FirstObj P X)
#check (CategoryTheory.Equalizer.Presieve.Arrows.firstMap P X π :
  CategoryTheory.Equalizer.Presieve.Arrows.FirstObj P X ⟶
    CategoryTheory.Equalizer.Presieve.Arrows.SecondObj P X π)
#check (CategoryTheory.Equalizer.Presieve.Arrows.secondMap P X π :
  CategoryTheory.Equalizer.Presieve.Arrows.FirstObj P X ⟶
    CategoryTheory.Equalizer.Presieve.Arrows.SecondObj P X π)
#check (CategoryTheory.Equalizer.Presieve.Arrows.FirstObj P X : Type w)
#check (CategoryTheory.Equalizer.Presieve.Arrows.SecondObj P X π : Type w)
