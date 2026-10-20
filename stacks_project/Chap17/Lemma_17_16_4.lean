/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 17.16.4 (01CD): pullback of the tensor product of two module sheaves is canonically
isomorphic to the tensor product of their pullbacks. -/
@[stacks 01CD]
#check @RingedSpace.Hom.pullbackTensorIso

/- The comparison is natural in both module arguments. -/
#check @RingedSpace.Hom.pullbackTensorNatIso

/- Module pullback carries the canonical strong-monoidal structure without additional
source-facing instance assumptions. -/
#check @RingedSpace.Hom.pullbackMonoidal

/- The corresponding tensor comparison morphism is available separately. -/
#check @RingedSpace.Hom.pullbackTensorComparison
