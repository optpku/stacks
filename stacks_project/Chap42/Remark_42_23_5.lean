/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.CohQuotientK0

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

open Scheme.Modules

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Remark 42.23.5

The canonical map from `CH_k(X)` to `K₀(Coh(X) / Coh≤k-1(X))` is obtained by composing
the map to the bounded coherent quotient with the bounded-to-full quotient transition.
The remark asserts neither injectivity nor that the kernel is torsion.
-/
@[stacks 02SD]
#check (AlgebraicGeometry.ChowGroup.toCohQuotientK0 f δ k :
    @AlgebraicGeometry.ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k →+
      AlgebraicGeometry.Scheme.Modules.CohQuotientK0 f δ (k - 1))

end AlgebraicGeometry.ChowGroup
