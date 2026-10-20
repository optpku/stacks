/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Invertible.Decomposition
import StacksCheckRecall

@[expose] public section

/- Lemma 20.52.2 (0FPG), conditions (1) and (2): an object of `D(𝒪_X)` is
tensor-invertible exactly when it admits the canonical locally finite decomposition by shifted
invertible modules over factor ring sheaves. -/
@[stacks 0FPG "(1) iff (2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isInvertible_iff_hasDecomposition

/- Lemma 20.52.2 (0FPG): every tensor-invertible object of `D(𝒪_X)` is perfect. -/
@[stacks 0FPG "perfectness"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_of_isInvertible

/- Lemma 20.52.2 (0FPG), conditions (2) and (3): when all stalk rings are local, the
decomposition condition is equivalent to being locally a shift of an invertible module. -/
@[stacks 0FPG "(2) iff (3)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.hasDecomposition_iff_isLocallyShiftedInvertible_of_stalk_isLocalRing

/- Lemma 20.52.2 (0FPG): under the local-stalk hypothesis, conditions (1), (2), and (3) are
pairwise equivalent. -/
@[stacks 0FPG "(1), (2), (3)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.invertible_tfae_of_stalk_isLocalRing

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.InvertibleFamily
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.HasInvertibleDecomposition
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyShiftedInvertible
