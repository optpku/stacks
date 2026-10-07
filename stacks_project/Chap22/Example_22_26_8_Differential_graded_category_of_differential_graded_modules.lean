module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/- Example 22.26.8 (Differential graded category of differential graded modules) (09LC): right
differential graded modules over a cochain differential graded algebra form a differential
graded category whose homogeneous morphisms are `GradedHom`. -/
@[stacks 09LC] #check
  (DifferentialGradedModule.differentialGradedCategory A :
    DifferentialGradedCategory R (DifferentialGradedModule.{u, v} A))

/- The Hom object is the module of homogeneous right-linear graded maps. -/
#check @DifferentialGradedModule.differentialGradedCategory_hom

/- The Hom differential is the standard signed commutator with the module differentials. -/
#check @DifferentialGradedModule.gradedHomDifferential_apply

/- Closed degree-`k` maps identify with module morphisms into the `k`th shift. -/
#check @DifferentialGradedModule.closedGradedHomEquivShiftHom
