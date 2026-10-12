/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Acyclicity
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.6 (01ET): if a module is acyclic on all nonempty finite intersections of an open
cover, there is one derived comparison whose canonical degree projections are all isomorphisms. -/
@[stacks 01ET]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclicOnIntersections.exists_comparison

/- Object-level bridge for downstream calculations. -/
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclicOnIntersections.isIsomorphic_cohomology

#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclicOnIntersections
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsUnderlyingAcyclicOnIntersections
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclicOnIntersections.iff_underlying
#check @AlgebraicGeometry.RingedSpace.ModuleCech.IsAcyclicOnIntersections.of_underlying
