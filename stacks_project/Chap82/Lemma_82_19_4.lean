/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernProperPushforward

/-!
# Proper pushforward of first-Chern intersection on algebraic spaces

In Situation 82.2.1, proper pushforward of cycles commutes with intersecting
by the first Chern class of an invertible sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.19.4: In Situation 82.2.1 let `X`, `Y / B` be good. Let
`f : X ⟶ Y` be a proper morphism over `B`. Let `α` be a `(k + 1)`-cycle
on `X`. Let `L` be an invertible sheaf on `Y`. Then
`f_*(c1((Modules.pullback f).obj L) ∩ α) = c1(L) ∩ f_* α` in
`chowGroup pY δ k`. The left-hand side pushes forward the first-Chern Chow
class; the right-hand side caps `L` against the cycle-level proper
pushforward of `α`. -/
@[stacks 0EQT] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_firstChernClassCap :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX)
    (L : Y.Modules) [isInvertibleObject L]
    (k : ℤ) (α : cycleGroup pX δ (k + 1)),
    ChowGroup.properPushforward pX pY δ f hf k
        (firstChernClassCap pX δ ((Modules.pullback f).obj L) k α) =
      firstChernClassCap pY δ L k
        (properPushforwardHom pX pY δ f hf (k + 1) α))

end AlgebraicGeometry.AlgebraicSpace.Hom
