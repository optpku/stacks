module

public import Mathlib.GroupTheory.GroupAction.Defs
public import ReasLib.RingTheory.Derivation.Action
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Action
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Differential

/-!
# Orbits of the differential of a formal object

The differential of a formal object is equivariant for residue-field derivations.
Orbit bijectivity consists of orbit surjectivity and orbit injectivity.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace FormalObject

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

noncomputable section

/-- The differential of a formal object is equivariant for the residue-derivation
actions on base derivations and the tangent space. -/
theorem differential_vadd (ξ : FormalObject p) [Functor.IsPredeformationCategory p]
    (derivation : Derivation Λ k k) (baseDerivation : Derivation Λ ξ.base.carrier k) :
    differential ξ (derivation +ᵥ baseDerivation) =
      derivation +ᵥ differential ξ baseDerivation := sorry

/-- A formal object has orbit-bijective differential if every tangent vector is in the
orbit of an image and two images share an orbit exactly when their derivations do. -/
def BijectiveDifferentialOnOrbits (ξ : FormalObject p) [Functor.IsPredeformationCategory p] :
    Prop :=
  (∀ value, ∃ derivation,
    value ∈ AddAction.orbit (Derivation Λ k k) (differential ξ derivation)) ∧
    (∀ left right,
      differential ξ left ∈ AddAction.orbit (Derivation Λ k k) (differential ξ right) ↔
        left ∈ AddAction.orbit (Derivation Λ k k) right)

/-- Orbit bijectivity of the differential is the conjunction of orbit surjectivity
and orbit injectivity. -/
theorem bijectiveDifferentialOnOrbits_iff (ξ : FormalObject p)
    [Functor.IsPredeformationCategory p] :
    BijectiveDifferentialOnOrbits ξ ↔
      (∀ value, ∃ derivation,
        value ∈ AddAction.orbit (Derivation Λ k k) (differential ξ derivation)) ∧
        (∀ left right,
          differential ξ left ∈ AddAction.orbit (Derivation Λ k k) (differential ξ right) ↔
            left ∈ AddAction.orbit (Derivation Λ k k) right) := Iff.rfl

end

end FormalObject
