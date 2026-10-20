module

public import ReasLib.CategoryTheory.Graded.Functor
import StacksCheckRecall

universe x w v u u'

open CategoryTheory

variable {R : Type w} [Semiring R]
variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {C : Type u} {D : Type u'}
variable [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
variable [GradedCategory R C ι] [GradedCategory R D ι]
variable (F : C ⥤ D)

/- Definition 22.25.2 [09L3]: degree-preserving linear functors between graded categories
are canonically represented by `Functor.Graded`. -/
@[stacks 09L3] #check (Functor.Graded ι R F : Prop)
