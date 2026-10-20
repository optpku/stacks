module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Kernel
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v w

variable {R : Type u} [CommRing R] (A : CochainDGAlgebra.{u, w} R)

/- Lemma 22.22.1 (09KW): acyclic right differential graded `A`-modules form a triangulated,
retract-closed object property, and their cone-defined weak equivalences are precisely the
quasi-isomorphisms. -/
@[stacks 09KW]
#check DifferentialGradedModule.QuasiIso.eq_trW.{u, v} A

#check DifferentialGradedModule.Derived.Q_kernel_eq_acyclic.{u, v} A

#check DifferentialGradedModule.Derived.Q_obj_isZero_iff.{u, v} A

#check (inferInstance :
  (DifferentialGradedModule.Homotopy.acyclic.{u, v} A).IsTriangulated)

#check (inferInstance :
  (DifferentialGradedModule.Homotopy.acyclic.{u, v} A).IsStableUnderRetracts)

#check (inferInstance :
  (DifferentialGradedModule.quasiIso.{u, v} A).HasTwoOutOfThreeProperty)
