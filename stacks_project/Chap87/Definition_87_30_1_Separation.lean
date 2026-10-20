/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

/-!
# Separation axioms for morphisms of formal algebraic spaces

A morphism of formal algebraic spaces is separated or quasi-separated according
as its relative diagonal is a closed immersion or quasi-compact, in the
representable sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The compatibility name for the relative pullback diagonal of a morphism of
presheaves over a scheme. -/
noncomputable def diagonal {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    X ⟶ pullback f f :=
  pullback.diagonal f

end AlgebraicGeometry.FormalAlgebraicSpace
