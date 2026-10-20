/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.SquareZero

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules.RingedSite

/- Lemma 20.25.5 (0B8S): the connecting map of a locally surjective square-zero extension of
commutative-ring sheaves is a derivation from global functions to first cohomology of the kernel.
The source word "surjection" is represented by `Sheaf.IsLocallySurjective`, not by the weaker
categorical class `Epi`; no splitting of the extension is chosen. -/
@[stacks 0B8S "square-zero boundary derivation"]
#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero.boundaryDerivation

#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero.boundaryLinearMap
#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero.H1_kernelEquiv
#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero.H1_isomorphic_kernel
#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero.boundaryLinearMap_leibniz
#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.SquareZero.boundaryDerivation_toLinearMap

end
