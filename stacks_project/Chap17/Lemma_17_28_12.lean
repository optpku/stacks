/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
import StacksCheckRecall

@[expose] public section

/-! Lemma 17.28.12 (08RU): a commutative square of ringed spaces determines a canonical
comparison f^* Ω[X/S] ⟶ Ω[X'/S']; its adjoint sends d[X/S](t) to d[X'/S'](f^♯ t), and this
property uniquely characterizes the comparison. -/
@[stacks 08RU]
#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.comparison

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.comparisonSection

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.comparisonDerivation

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.comparisonAdjoint

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.IsComparison

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.comparison_d

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.eq_comparison

#check @AlgebraicGeometry.RingedSpace.Hom.Differentials.existsUnique_comparison
