/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials.Composition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
import StacksCheckRecall

@[expose] public section

/-! Lemma 17.28.13 (01UW): the comparison morphism on relative differentials is compatible with
composition of commutative squares, after the canonical identification of composite and iterated
pullback. -/
@[stacks 01UW]
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.comparison_comp

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.comparisonComp

#check @SheafOfModules.RingedSite.RelativeDifferentials.map_comp_coherent
