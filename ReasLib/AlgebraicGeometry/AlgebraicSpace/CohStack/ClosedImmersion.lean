/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.QuasiFinite

/-!
# Closed immersions induced by coherent-sheaf pushforward
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Pushforward along a closed immersion between algebraic spaces separated
and of finite presentation over `B` induces a closed immersion of their
groupoid fibrations of coherent sheaves. -/
instance instClosedImmersion_map (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y] :
    Hom.ClosedImmersion (map π y) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
