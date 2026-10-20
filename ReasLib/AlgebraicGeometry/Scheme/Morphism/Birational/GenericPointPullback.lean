/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational

/-!
# Birational Pullbacks at Generic Points

This module records the behavior of a birational morphism after base change to
the local scheme at a generic point of the target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For a birational morphism between schemes with finitely many irreducible components,
the pullback projection over the local scheme at a target generic point is an isomorphism. -/
theorem isIso_pullbackSnd_fromSpecStalk_of_isBirational
    {X Y : Scheme.{u}} [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f] (y : genericPoints Y) :
    IsIso (pullback.snd f (Y.fromSpecStalk y)) := sorry

end AlgebraicGeometry
