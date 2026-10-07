module

import StacksCheckRecall
import stacks_project.Chap42.Remark_42_34_7_Cutoff

/- Remark 42.34.7 (1): the degreewise cutoff family `A⁽ᵖ⁾(Z ⟶ X)`. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff

/- Remark 42.34.7 (2): multiplication of a relative class by an ambient class. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMulAmbient
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMulAmbient_apply

/- Remark 42.34.7 (3): multiplication of an ambient class by a relative class. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.ambientMulRelative
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.ambientMulRelative_apply

/- Remark 42.34.7 (4): multiplication of two relative classes. -/
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMul
@[stacks 0FA0] #check AlgebraicGeometry.BivariantClass.Cutoff.relativeMul_apply

/- The claimed multiplication into cutoff `max p q` is not asserted here: when two
ambient degrees cross that cutoff, the source supplies no ambient-to-relative map. -/
