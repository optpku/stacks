/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Injective
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.1 (1) (01EP): for an injective module sheaf and an open cover of `U`, degree-zero
Cech cohomology is the module of sections on `U`. The module-valued owner keeps the scalar ring. -/
@[stacks 01EP]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.zero_isomorphic_evaluation_of_injective

/- General union/evaluation bridge, useful beyond the injective specialization. -/
#check @AlgebraicGeometry.RingedSpace.ModuleCech.zero_isomorphic_evaluation

/- Underlying additive bridge retained for clients that intentionally forget scalars. -/
#check @AlgebraicGeometry.RingedSpace.ModuleCech.zero_isomorphic_sections
#check @AlgebraicGeometry.RingedSpace.ModuleCech.zero_isomorphic_sections_functor

/- Lemma 20.11.1 (2) (01EP): injective module sheaves have vanishing positive-degree Cech
cohomology for every indexed open family. -/
@[stacks 01EP]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.isZero_of_injective_evaluation

#check @AlgebraicGeometry.RingedSpace.ModuleCech.isZero_succ_of_injective
