/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme Closed Immersions from Ringed-Space Closed Immersions

This bridge upgrades the reusable ringed-space closed-immersion condition to
mathlib's closed-immersion condition for a scheme morphism.
-/

@[expose] public section

open CategoryTheory TopCat TopCat.Sheaf
open AlgebraicGeometry
open TopCat.Presheaf

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsClosedImmersion

/-- A scheme morphism whose underlying ringed-space morphism is a closed
immersion is a closed immersion of schemes. -/
@[stacks 01C2 "scheme bridge"]
instance toScheme
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [RingedSpace.IsClosedImmersion f.toShHom] : AlgebraicGeometry.IsClosedImmersion f := sorry

end AlgebraicGeometry.RingedSpace.IsClosedImmersion
