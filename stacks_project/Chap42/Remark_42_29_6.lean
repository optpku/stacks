/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TrivialRestriction

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
  (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)
  (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ)) (k : ℤ)

/- Remark 42.29.6: If `ℒ` restricts trivially to its zero scheme `Z(s)`, there is a
canonical additive map from degree-`k + 1` cycles on `X` to degree-`k` cycles on `Z(s)`
which sends each integral generator contained in `Z(s)` to zero. -/
@[stacks 0B6Z] #check (AlgebraicGeometry.Scheme.Modules.trivialGysin p δ ℒ s htriv k :
  CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k)

end AlgebraicGeometry.Scheme.Modules
