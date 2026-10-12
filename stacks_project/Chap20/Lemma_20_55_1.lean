/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.1 (0GT3) (1): a locally principal regular ideal sheaf is finite locally free of
rank one and hence tensor-invertible. -/
@[stacks 0GT3 "(1), rank one"]
#check @IdealSheaf.IsRegularPrincipal.rankOne

@[stacks 0GT3 "(1), invertible"]
#check @IdealSheaf.IsRegularPrincipal.isInvertible

/- Lemma 20.55.1 (0GT3) (2): if all structure-sheaf stalks are local rings, a tensor-invertible
ideal sheaf is locally principal regular. -/
@[stacks 0GT3 "(2)"]
#check @IdealSheaf.IsRegularPrincipal.ofIsInvertible

@[stacks 0GT3 "equivalence"]
#check @IdealSheaf.isRegularPrincipal_iff_isInvertible
