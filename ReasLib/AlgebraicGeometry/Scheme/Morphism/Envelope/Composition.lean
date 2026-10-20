/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsEnvelope

/-- The composite of two envelopes is an envelope. -/
instance comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsEnvelope f] [IsEnvelope g] : IsEnvelope (f ≫ g) := sorry

end AlgebraicGeometry.IsEnvelope
