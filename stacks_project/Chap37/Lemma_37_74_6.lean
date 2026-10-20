/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.LocallyQuasiFinite.Semicontinuity

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/- Lemma 37.74.6: for a separated, locally quasi-finite, universally open morphism,
the geometric fibre-component count is lower semicontinuous on the target. -/
@[stacks 0F36] #check
  (AlgebraicGeometry.LocallyQuasiFinite.lowerSemicontinuous_geometricFiberComponentCount :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [IsSeparated f] [UniversallyOpen f],
      LowerSemicontinuous f.geometricFiberComponentCount)

end AlgebraicGeometry.LocallyQuasiFinite
