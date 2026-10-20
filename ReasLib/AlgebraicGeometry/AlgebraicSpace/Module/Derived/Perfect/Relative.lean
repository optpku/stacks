/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Relative.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# Relatively perfect derived modules on algebraic spaces

Relative perfectness combines pseudo-coherence with local finite Tor dimension
over the inverse-image structure sheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The object property of being perfect relative to a flat, locally finitely presented
morphism of algebraic spaces. -/
def perfectRelativeTo (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty (ModuleDerived X) :=
  (fun E ↦ IsPseudoCoherent X E) ⊓ locallyFiniteTorDimensionOver f

/-- A derived `𝒪_X`-module is `Y`-perfect when it belongs to `perfectRelativeTo f`. -/
abbrev IsPerfectRelativeTo (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (E : ModuleDerived X) : Prop :=
  perfectRelativeTo f E

/-- Relative perfectness over a flat, locally finitely presented morphism `f : X ⟶ Y`
is equivalent to pseudo-coherence over `𝒪_X` and local finite Tor dimension over `f⁻¹𝒪_Y`. -/
theorem isPerfectRelativeTo_iff (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (E : ModuleDerived X) :
    IsPerfectRelativeTo f E ↔
      IsPseudoCoherent X E ∧ locallyFiniteTorDimensionOver f E := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
