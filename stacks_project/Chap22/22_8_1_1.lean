module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Triangle
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, w} A))
variable (sigma : DifferentialGradedModule.ShortComplex.GradedSplitting S)

/- Equation 22.8.1.1 (09K7): a chosen graded `A`-linear splitting of an admissible short exact
sequence of differential graded modules determines the displayed triangle
`K ⟶ L ⟶ M ⟶ K[1]` in the intrinsic DG homotopy category. -/
@[stacks 09K7]
#check (DifferentialGradedModule.ShortComplex.associatedTriangleK S sigma :
  Triangle (K R (DifferentialGradedModule.{u, w} A)))

/- Its third arrow is represented by the explicit connecting DG-module morphism. -/
#check @DifferentialGradedModule.ShortComplex.GradedSplitting.connectingHom

/- Admissibility is short exactness together with the existence of such a graded `A`-linear
splitting. -/
#check @DifferentialGradedModule.isAdmissibleShortExact_iff_nonempty_gradedSplitting
