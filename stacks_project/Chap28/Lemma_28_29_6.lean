module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.FiniteSet
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The underlying set of the nonvanishing locus of a global section of a tensor power. -/
abbrev tensorPowerSectionNonvanishingSet
    {X : Scheme.{u}} (L : X.Modules) (n : ℕ)
    (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)) : Set X :=
  RingedSpace.sectionNonvanishingLocus X.toRingedSpace
    (RingedSpace.TensorPower.sheaf L n)
    (RingedSpace.sectionFromTop (RingedSpace.TensorPower.sheaf L n) s)

/-- A tensor-power section identifies an affine nonvanishing open containing a point. -/
abbrev TensorPowerSectionAffineNonvanishingAt
    {X : Scheme.{u}} (L : X.Modules) (n : ℕ+)
    (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)) (U : X.Opens) (x : X) : Prop :=
  (U : Set X) = tensorPowerSectionNonvanishingSet L n s ∧
    AffineOpenNeighborhood x U

end AlgebraicGeometry.Scheme.Modules

/- Lemma 28.29.6: for an ample invertible module on a scheme, every finite set contained in an
open lies in an affine nonvanishing open of a positive tensor-power section which is itself
contained in the prescribed open. -/
@[stacks 09NV] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.exists_affineNonvanishingOpen_between :
    ∀ {X : Scheme.{u}} {L : X.Modules}
      [hL : AlgebraicGeometry.Scheme.Modules.Invertible L],
      AlgebraicGeometry.Scheme.Modules.IsAmple L →
        ∀ (E : Set X), E.Finite →
          ∀ (W : X.Opens), E ⊆ (W : Set X) →
            ∃ n : ℕ+,
              ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
                IsAffineOpen (hL.nonvanishingOpen s) ∧
                  E ⊆ (hL.nonvanishingOpen s : Set X) ∧ hL.nonvanishingOpen s ≤ W)
