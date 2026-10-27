/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.LocalGeneration
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Pullback.LocalGeneration
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local generation of pulled-back ideals on locally ringed spaces
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- Pullback along a locally ringed-space morphism preserves local generation by sections. -/
@[stacks 01HQ "locally ringed-space local generation under pullback"]
theorem IdealSubobject.pullback_isLocallyGenerated
    {X Y : LocallyRingedSpace.{u}} (I : IdealSubobject X) (f : Y ⟶ X)
    (hI : I.IsLocallyGeneratedBySections) :
    (I.pullback f).IsLocallyGeneratedBySections := sorry

end AlgebraicGeometry.LocallyRingedSpace
