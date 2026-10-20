module

public import ReasLib.CategoryTheory.Fibered.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe uA uB uC vA vB vC

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable (F : A ⥤ B) (G : B ⥤ C) [F.IsFibered] [G.IsFibered]

/- Lemma 4.33.12: the composite of two fibred functors is fibred. -/
@[stacks 09WV]
#check (CategoryTheory.Functor.IsFibered.compFunctor F G : (F ⋙ G).IsFibered)
