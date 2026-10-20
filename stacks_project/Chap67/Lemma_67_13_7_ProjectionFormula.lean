/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula

/-! # Projection-formula comparison for algebraic-space ringed topoi

The public owner retains the explicit sectionwise tensor maps and their actual adjunction mate.
The full source lemma facade continues to carry its original tag and subclauses.
-/

@[expose] public section

#check @AlgebraicGeometry.AlgebraicSpace.toRingedToposHom
#check @AlgebraicGeometry.AlgebraicSpace.moduleTensorSheafifyIso
#check @AlgebraicGeometry.AlgebraicSpace.modulePushforward_tensorComparison
#check @AlgebraicGeometry.AlgebraicSpace.modulePullbackTensorComparison
#check @AlgebraicGeometry.AlgebraicSpace.projectionFormula
#check @AlgebraicGeometry.AlgebraicSpace.projectionFormula_spec
