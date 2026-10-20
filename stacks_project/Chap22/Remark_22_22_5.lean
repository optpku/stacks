module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R] (A : CochainDGAlgebra.{u, v} R)

/- Remark 22.22.5 (0FQE): arbitrary coproducts, two-out-of-three for distinguished triangles,
and the shifts `A[k]` propagate a property to every object of the canonical derived category
`DifferentialGradedModule.Derived.Category A`. -/
@[stacks 0FQE]
#check DifferentialGradedModule.Derived.holds_of_regularShifts A
  (DifferentialGradedModule.Derived.Q A)

/- The images of all shifts of the regular module form a localizing generating family in the
canonical derived category. -/
#check DifferentialGradedModule.Derived.regularShifts_isLocalizingGenerator A
  (DifferentialGradedModule.Derived.Q A)
