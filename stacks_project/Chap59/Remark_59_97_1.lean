/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Etale.Kunneth
import StacksCheckRecall

@[expose] public section

/- Remark 59.97.1: the canonical map for a cartesian square, with arbitrary commutative
coefficients.  Inverse/direct images and composition comparisons are the geometric
constructions. Supplied derived adjunctions and the two-variable tensor comparison carry
normalization witnesses against the actual maps on complexes. -/
@[stacks 0F1E] #check AlgebraicGeometry.Scheme.Etale.Kunneth.map

#check AlgebraicGeometry.Scheme.Etale.Kunneth.leftLeg
#check AlgebraicGeometry.Scheme.Etale.Kunneth.rightLeg
#check AlgebraicGeometry.Scheme.Etale.Kunneth.adjointMap
#check AlgebraicGeometry.Scheme.Etale.Kunneth.map_eq
#check AlgebraicGeometry.Scheme.Etale.Kunneth.map_adjoint_spec
