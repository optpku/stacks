module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone
public import ReasLib.Algebra.Category.DifferentialGraded.DirectSum
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} [DifferentialGradedCategory.{u, v, w} R A]
variable [HasBinaryBiproducts (Comp R A)]
variable [HasShift (Comp R A) ℤ]
variable [ShiftCompatibility R A]

/- Situation 22.27.2 (09QJ): `Comp R A` has binary differential graded direct sums and shifts,
the shifts are compatible with the DG enrichment, and a cone system assigns to every
`f : x ⟶ y` a split short complex `y ⟶ c(f) ⟶ x⟦1⟧` whose canonical boundary is
`f⟦1⟧'`. -/
@[stacks 09QJ]
#check (AdmissibleBoundary.ConeSystem (R := R) (A := A) : Type _)

#check (inferInstance : HasBinaryBiproducts (Comp R A))

#check @CompBoundaryAssignment.AdmissibleCones.cone
#check @AdmissibleBoundary.ConeSystem.boundary_eq
