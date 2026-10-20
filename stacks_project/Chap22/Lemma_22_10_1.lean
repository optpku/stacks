module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R] (A : CochainDGAlgebra.{u, w} R)

/- Lemma 22.10.1 (09KH): the homotopy category of right differential graded `A`-modules,
with its canonical shifts and mapping-cone triangles, is pretriangulated. -/
@[stacks 09KH]
#check (inferInstance : Pretriangulated (K R (DifferentialGradedModule.{u, v} A)))

/- Its distinguished triangles are intrinsically the triangles isomorphic to explicit
differential graded mapping-cone triangles. -/
#check DifferentialGradedModule.Homotopy.distinguished A

#check @DifferentialGradedModule.Homotopy.mappingCone_triangleK_distinguished
