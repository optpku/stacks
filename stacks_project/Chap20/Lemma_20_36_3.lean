module

public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.GlobalSections
import StacksCheckRecall

@[expose] public section

/- Lemma 20.36.3 (0BLB) is a direct specialization of the principal-torsion global-sections
owner.  The source's `n ≥ 1` presentation is the one-based bridge, while the limit, projection
kernel, finiteness, and regularity conclusions are shared ReasLib declarations. -/

#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Presentation
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.row
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPresented
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.isPresented_iff_one_le

@[stacks 0BLB "global-sections tower"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.GlobalSections.tower

@[stacks 0BLB "finite global-sections limit"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.GlobalSections.limit_finite

@[stacks 0BLB "regular scalar on the global-sections limit"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.GlobalSections.limit_isSMulRegular

@[stacks 0BLB "first-stage projection kernel"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.GlobalSections.projectionKernel_eq_smul_top
