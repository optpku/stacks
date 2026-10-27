/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Norm

/-! # Proper pushforward of principal cycles on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable [IsIntegral X]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- A dominant proper morphism over a quasi-separated universally catenary base
between good integral algebraic spaces of equal delta-dimension sends the
principal divisor of a rational-function unit to the principal divisor of its
induced function-field norm. -/
theorem properPushforward_principalDivisor {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (p : X ⟶ Y) [Proper p] [Dominant p] (hp : p ≫ pY = f)
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (φ : (RationalFunction X)ˣ) :
    properPushforwardHom f pY δ p hp (n - 1) (principalDivisor f δ n hX φ) =
      principalDivisor pY δ n hY (inducedRationalFunctionNorm p φ) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
