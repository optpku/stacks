module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.Criteria

/-!
# Powers of relatively ample modules

This module characterizes relative ampleness in terms of relative very ampleness of positive
tensor powers for finite-type morphisms over quasi-compact bases.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- For a finite-type morphism over a quasi-compact base, an invertible module is relatively
ample if and only if some positive tensor power is relatively very ample, equivalently if every
sufficiently high tensor power is relatively very ample. -/
theorem relativeAmpleness_tfae_tensorPow_relativeVeryAmpleness
    [CompactSpace S] [Scheme.Hom.FiniteType f] [Scheme.Modules.Invertible L] :
    List.TFAE [
      RelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧
        RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d)] := sorry

end AlgebraicGeometry
