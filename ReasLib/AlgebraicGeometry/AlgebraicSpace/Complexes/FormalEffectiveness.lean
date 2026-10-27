/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Category

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- Over a locally Noetherian base scheme, every compatible formal system of
relatively perfect complexes with fibrewise vanishing negative self-Ext on a
proper, flat, finitely presented algebraic space is effective. -/
theorem strongFormalEffectiveness {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [Proper f] [Flat f] [FinitePresentation f]
    (ξ : FormalObjectSystem (p f)) : ξ.IsEffective := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
