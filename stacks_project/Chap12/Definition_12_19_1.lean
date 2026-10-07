module

public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.GradedPiece
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasCokernels C]
variable (A B : FilteredObject C) (f : A ⟶ B) (p : ℤ)

/- Definition 12.19.1 [0121] (1): a filtered object owns a decreasing integer-indexed family of
subobjects. -/
@[stacks 0121]
#check (A.filtration : DecreasingFiltration A.obj)

/- Definition 12.19.1 [0121] (2): the stage family is antitone. -/
@[stacks 0121]
#check (A.filtration.antitone : Antitone A.filtration.stage)

/- Definition 12.19.1 [0121] (3): a filtered morphism has an induced map on every stage. -/
@[stacks 0121]
#check (f.stageMap p : A.stage p ⟶ B.stage p)

/- Definition 12.19.1 [0121] (4): finite filtrations have both a top and a zero stage. -/
@[stacks 0121]
#check (A.IsFinite : Prop)

/- Definition 12.19.1 [0121] (5): consecutive stages define the graded pieces and the associated
graded object. -/
@[stacks 0121]
#check (A.gradedPiece p : C)
#check (A.associatedGraded : GradedObject ℤ C)

end CategoryTheory
