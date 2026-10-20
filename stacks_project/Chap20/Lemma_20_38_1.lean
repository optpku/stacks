/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Truncation.Resolution

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation.Resolution

/-
Lemma 20.38.1: if the negative cohomology sheaves of a complex have uniformly vanishing higher
cohomology on an open basis, then the canonical map to the inverse limit of any injective
lower-truncation resolution is a quasi-isomorphism.

The canonical owner uses module-valued open cohomology; `SheafNegative` and
`negative_iff_sheafNegative` provide the exact underlying-additive-sheaf formulation used in the
source.
-/

@[stacks 071B "Lemma 20.38.1: convergence of an injective lower-truncation resolution"]
#check @intoLimit_quasiIso_ofSheaves

@[stacks 071B "basiswise negative cohomology condition for sheaves"]
#check @Basis.SheafNegative
@[stacks 071B "module and underlying-sheaf negative conditions"]
#check @Basis.negative_iff_sheafNegative
@[stacks 071B "lower-truncation resolution comparison"]
#check @intoLimit_quasiIso

end
