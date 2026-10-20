module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Admissible
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}
variable {K L : DifferentialGradedModule.{u, v} A}
variable (f : K ⟶ L)

/- Lemma 22.9.1 (09KB): the explicit DG-module cone row
`L ⟶ mappingCone f ⟶ K[1]` is admissible, and its associated triangle has maps
`inclusion f`, `projection f`, and `shiftMap f 1`. -/
@[stacks 09KB]
#check (DifferentialGradedModule.MappingCone.associatedTriangle_eq f :
  DifferentialGradedModule.ShortComplex.associatedTriangle
      (DifferentialGradedModule.MappingCone.shortComplex f)
      (DifferentialGradedModule.MappingCone.gradedSplitting f) =
    Triangle.mk (DifferentialGradedModule.MappingCone.inclusion f)
      (DifferentialGradedModule.MappingCone.projection f)
      (DifferentialGradedModule.shiftMap f 1))

/- The canonical cone row and its graded `A`-linear splitting are reusable data owners. -/
#check @DifferentialGradedModule.MappingCone.shortComplex
#check @DifferentialGradedModule.MappingCone.gradedSplitting

/- Admissibility retains the graded `A`-module action rather than forgetting to degreewise
`R`-modules. -/
#check @DifferentialGradedModule.MappingCone.isAdmissibleShortExact
