/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
import ReasLib.Topology.Specialization.Dimension

open AlgebraicGeometry

universe u

section

variable (S : Scheme.{u}) [UniversallyCatenary S]
variable (δ : S → ℤ) [IsDimensionFunction δ]

/- Situation 42.7.1: `S` is a universally catenary scheme, hence locally Noetherian,
and `δ : S → ℤ` is a chosen dimension function. -/
@[stacks 02QL] #check (AlgebraicGeometry.UniversallyCatenary S : Prop)

#check (δ : S → ℤ)
#check (inferInstance : IsDimensionFunction δ)
#check (inferInstance : AlgebraicGeometry.IsLocallyNoetherian S)

end
