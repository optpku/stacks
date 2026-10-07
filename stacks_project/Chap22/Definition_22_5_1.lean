module

public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R] {C : Type v}
variable [DifferentialGradedCategory.{u, v, w} R C]
variable {X Y : C} (f g : CompHom X Y)

/- Definition 22.5.1 (09JN): two closed degree-zero morphisms in a differential graded
category are homotopic when their difference is the differential of a degree-`-1` morphism.
For the DG category of right modules over a cochain DGA, this is the source relation on
DG-module morphisms. -/
@[stacks 09JN] #check (Homotopic X Y f g : Prop)
