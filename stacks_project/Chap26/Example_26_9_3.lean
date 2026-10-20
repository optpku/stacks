module

public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.AffinePlane
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable (k : Type u) [Field k]

/- Example 26.9.3: the affine plane with its origin removed has the same global functions as the
affine plane, but is not affine. This is the two-coordinate specialization of the reusable
punctured-affine-space API. -/
@[stacks 01IL "punctured affine plane"]
#check PuncturedAffinePlane.puncturedOpen k
@[stacks 01IL "affine-plane/polynomial-spectrum comparison"]
#check PuncturedAffineSpace.coordinateModelIso (ULift.{u} (Fin 2)) k
@[stacks 01IL "affine-plane origin algebra map"]
#check PuncturedAffinePlane.evalAtOriginAlgHom k
#check PuncturedAffineSpace.mem_originIdeal_iff (Fin 2) k
@[stacks 01IL "puncture comparison"]
#check PuncturedAffineSpace.coordinateModelIso.preimage_puncturedOpen
  (ULift.{u} (Fin 2)) k
@[stacks 01IL "two-chart cover"]
#check PuncturedAffinePlane.puncturedOpen_eq_chartX_sup_chartY k
@[stacks 01IL "affine coordinate charts"]
#check PuncturedAffinePlane.chartX_isAffineOpen k
#check PuncturedAffinePlane.chartY_isAffineOpen k
@[stacks 01IL "coordinate-chart intersection"]
#check PuncturedAffinePlane.chartX_inf_chartY k
#check PuncturedAffinePlane.chartXY_isAffineOpen k
#check PuncturedAffinePlane.puncturedOpen.coe_eq_compl_origin k
@[stacks 01IL "sheaf condition on the two-chart cover"]
#check (PuncturedAffinePlane.affinePlane k).sheaf.isLimitPullbackCone
  (PuncturedAffinePlane.chartX k) (PuncturedAffinePlane.chartY k)
@[stacks 01IL "global sections"]
#check PuncturedAffineSpace.globalSectionsComparison.isIso (ULift.{u} (Fin 2)) k
#check PuncturedAffinePlane.globalSectionsComparison k
@[stacks 01IL "affine-plane global sections"]
#check PuncturedAffinePlane.globalSectionsComparison.isIso k
@[stacks 01IL "nonaffineness"] #check PuncturedAffinePlane.not_isAffine k
