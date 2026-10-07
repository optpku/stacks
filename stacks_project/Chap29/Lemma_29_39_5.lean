module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.Power
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.39.5: for a finite-type morphism of schemes with quasi-compact base, an invertible
module is relatively ample if and only if some positive tensor power is relatively very ample,
equivalently if every sufficiently high tensor power is relatively very ample. -/
@[stacks 01VU] #check
  (AlgebraicGeometry.relativeAmpleness_tfae_tensorPow_relativeVeryAmpleness :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [CompactSpace S] [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [AlgebraicGeometry.Scheme.Modules.Invertible L],
      List.TFAE [
        AlgebraicGeometry.RelativelyAmple f L,
        ∃ d : ℕ, 1 ≤ d ∧
          AlgebraicGeometry.RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d),
        ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
          AlgebraicGeometry.RelativelyVeryAmple f (RingedSpace.TensorPower.sheaf L d)])
