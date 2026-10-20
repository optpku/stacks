/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower

/-!
# Products of ideal sheaves on algebraic spaces

The product of two ideal subobjects of the structure sheaf is the image of the
ideal-sheaf action. Products of quasi-coherent ideals are quasi-coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IdealSubobject

/-- The product of two ideal subobjects of `𝒪_X`, obtained by the first
ideal-power action on the second. -/
noncomputable def mul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) : IdealSubobject X :=
  Modules.idealPowerSmulSubobject I J 1

/-- The product of ideal subobjects is the first ideal-power action on the
second. -/
theorem mul_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X) :
    mul I J = Modules.idealPowerSmulSubobject I J 1 :=
  rfl

/-- The product of ideal subobjects is the image of the action `I ⊗ J ⟶ 𝒪_X`. -/
theorem mul_spec {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X) :
    mul I J = imageSubobject (Modules.action I J.toModule ≫ J.arrow) :=
  rfl

end IdealSubobject

namespace IsQuasiCoherent

/-- The product of quasi-coherent ideal sheaves is quasi-coherent. -/
instance mul {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsQuasiCoherent (IdealSubobject.mul I J) :=
  sorry

end IsQuasiCoherent

end AlgebraicGeometry.AlgebraicSpace
