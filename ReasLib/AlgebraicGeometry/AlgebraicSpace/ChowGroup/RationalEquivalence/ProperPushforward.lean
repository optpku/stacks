/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RationalEquivalence

/-!
# Proper pushforward and rational equivalence

Proper pushforward preserves rational equivalence of cycles on good algebraic
spaces over a universally catenary, quasi-separated base with a dimension function.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Proper pushforward along a morphism over the base sends rationally equivalent
degree-`k` cycles on good algebraic spaces to rationally equivalent cycles. -/
theorem properPushforwardHom_rationallyEquivalent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ Y) [Proper p] (hp : p ≫ pY = pX) (k : ℤ)
    (α β : cycleGroup pX δ k)
    (hαβ : RationalEquivalence.RationallyEquivalent pX δ k α β) :
    RationalEquivalence.RationallyEquivalent pY δ k
      (properPushforwardHom pX pY δ p hp k α)
      (properPushforwardHom pX pY δ p hp k β) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
