/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Relative
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

/-!
# Relative perfectness over scheme morphisms

This file specializes relative perfectness of derived modules on ringed spaces to flat,
locally finitely presented morphisms of schemes.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- The object property of being perfect relative to a flat, locally finitely presented
scheme morphism. -/
def perfectRelativeTo (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  RingedSpace.ModuleDerived.perfectOver f.toShHom

/-- A derived `𝒪_X`-module is perfect relative to a flat, locally finitely presented
morphism `f : X ⟶ S` when it belongs to `perfectRelativeTo f`. -/
abbrev IsPerfectRelativeTo (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  perfectRelativeTo f E

/-- Relative perfectness over a scheme morphism is equivalent to pseudo-coherence over
`𝒪_X` and local finite Tor dimension after restriction to `f⁻¹𝒪_S`. -/
theorem isPerfectRelativeTo_iff (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsPerfectRelativeTo f E ↔
      RingedSpace.ModuleDerived.IsPseudoCoherent E ∧
        RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
          ((RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj E) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
