/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Comparison.Naturality
import StacksCheckRecall

@[expose] public section

/- Lemma 20.15.1 (01FD): compatible Cech-to-derived-sections comparisons can be chosen so that
the change-of-space square associated to an `f`-map and a refinement commutes; applying
cohomology gives the corresponding degreewise squares. -/
@[stacks 01FD]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Comparison.FMapSquare.nonempty

#check @AlgebraicGeometry.RingedSpace.ModuleCech.Comparison.FMapSquare.comm
#check @AlgebraicGeometry.RingedSpace.ModuleCech.Comparison.FMapSquare.degree_comm
