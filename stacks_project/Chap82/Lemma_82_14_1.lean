/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Principal.Pushforward

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.14.1: In Situation 82.2.1 let `X`, `Y / B` be good. Assume `X`, `Y`
are integral and `n = dim_δ(X) = dim_δ(Y)`. Let `p : X ⟶ Y` be a dominant proper
morphism. Let `φ ∈ (RationalFunction X)ˣ`. Set `g = Nm_{R(X)/R(Y)}(φ)`, the
image of `φ` under `inducedRationalFunctionNorm p`. Then `p_* div(φ) = div(g)`. -/
@[stacks 0EQ4] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_principalDivisor :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X]
      (δ : Points B → ℤ) [IsDimensionFunction δ] {Y : AlgebraicSpace S}
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      [IsIntegral Y] (p : X ⟶ Y) [Proper p] [Dominant p] (hp : p ≫ pY = f)
      (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
      (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
      (φ : (RationalFunction X)ˣ),
      properPushforwardHom f pY δ p hp (n - 1) (principalDivisor f δ n hX φ) =
        principalDivisor pY δ n hY (inducedRationalFunctionNorm p φ))
