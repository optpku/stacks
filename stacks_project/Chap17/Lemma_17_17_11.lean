/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.LocalFactorization
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.11 (08BK): a finite relation in a module sheaf which is flat at a point factors,
after shrinking around that point, through a finite free module. -/
@[stacks 08BK]
#check @AlgebraicGeometry.RingedSpace.Modules.FlatAt.existsFactorization

-- The source's family-of-sections formulation is retained as a computational bridge.
#check @AlgebraicGeometry.RingedSpace.Modules.FlatAt.existsMatrixFactorization
