/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

section

variable {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X) (I : IdealSubobject X)
variable [I.IsLocallyGeneratedBySections]

#synth (I.pullback f).IsLocallyGeneratedBySections

end

/- The theorem and canonical instance are inherited definitionally from the ringed-space owner. -/

end AlgebraicGeometry.LocallyRingedSpace
