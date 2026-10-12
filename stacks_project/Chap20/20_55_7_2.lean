/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Bockstein
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- 20.55.7.2 (0GT8): the Bockstein cohomology complex attached to an invertible ideal sheaf and a
derived module has the degreewise Bockstein terms and connecting differentials. -/
@[stacks 0GT8 "ideal-sheaf Bockstein cohomology complex"]
#check @IdealSheaf.Bockstein.complex

@[stacks 0GT8 "terms of the ideal-sheaf Bockstein complex"]
#check @IdealSheaf.Bockstein.complex_X

@[stacks 0GT8 "differential of the ideal-sheaf Bockstein complex"]
#check @IdealSheaf.Bockstein.complex_d

@[stacks 0GT8 "ideal-sheaf Bockstein differential"]
#check @IdealSheaf.Bockstein.d

end
