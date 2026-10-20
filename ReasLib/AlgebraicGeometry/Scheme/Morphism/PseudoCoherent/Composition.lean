/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Composition

/-!
# Composition of pseudo-coherent scheme morphisms

Pseudo-coherent morphisms of schemes are closed under composition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- Pseudo-coherent scheme morphisms are stable under composition. -/
instance instIsStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@PseudoCoherent.{u}) := sorry

/-- The composite of two pseudo-coherent scheme morphisms is pseudo-coherent. -/
instance comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [PseudoCoherent f] [PseudoCoherent g] : PseudoCoherent (f ≫ g) := sorry

end AlgebraicGeometry.PseudoCoherent
