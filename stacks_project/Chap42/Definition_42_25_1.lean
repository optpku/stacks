/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Definition 42.25.1: For an invertible module `ℒ` on a scheme `X` locally of finite
type over a universally catenary scheme with dimension function `δ`, intersection with
the first Chern class is an additive map from degree-`k + 1` cycles on `X` to degree-`k`
Chow classes. -/
@[stacks 02SO] #check
  (AlgebraicGeometry.Scheme.Modules.firstChernClassCap :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ] (k : ℤ),
      CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k)

end AlgebraicGeometry.Scheme.Modules
