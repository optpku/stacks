module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Distinguished
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (T : Triangle (K R (DifferentialGradedModule.{u, w} A)))

/- Definition 22.8.2 [09K8]: distinguished triangles in the homotopy category of DG modules
are precisely those associated to admissible short exact sequences. -/
@[stacks 09K8]
#check (DifferentialGradedModule.Homotopy.distinguished_iff_associated T :
  T ∈ distTriang (K R (DifferentialGradedModule.{u, w} A)) ↔
    ∃ S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, w} A),
      DifferentialGradedModule.IsAdmissibleShortExact S ∧
        DifferentialGradedModule.ShortComplex.IsAssociatedTriangle S T)

/- The associated-triangle predicate is independent of the chosen graded `A`-linear splitting. -/
#check @DifferentialGradedModule.ShortComplex.isAssociatedTriangle_iff_iso
