module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.InverseSystem.Adic
import StacksCheckRecall

@[expose] public section

/- Lemma 20.36.2 uses the reusable principal-torsion presentation of a sequential inverse
system.  The cohomology theorem keeps the source indexing: projection to stage `c` has kernel
`(f)^c H^p`; the generic topology bridge records this explicitly as adic projection kernels. -/

#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Presentation
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.row
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPresented
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.isPresented_iff
#check @AlgebraicGeometry.RingedSpace.GlobalSections.centerHom
#check @AlgebraicGeometry.RingedSpace.GlobalSections.instLinear
#check @AlgebraicGeometry.RingedSpace.moduleCohomologyTower
#check @CategoryTheory.SequentialInverseSystem.HasAdicKernels

@[stacks 0EHA "part 1"]
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.pow_eq_limitKernel

#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.hasAdicKernels

@[stacks 0EHA "part 2"]
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.limitTopology_eq_adic

/- The final topology comparison is reusable for any module-valued sequential inverse system
with the same one-based projection-kernel computation. -/
#check @CategoryTheory.SequentialInverseSystem.HasAdicKernels.limitTopology_eq_adic
