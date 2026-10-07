module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.PseudoDivisor

open CategoryTheory

universe u

/- Remark 42.29.3 (1): a pseudo-divisor is an invertible module, a closed support, and a
nowhere-vanishing section on the open complement. -/
@[stacks 0B7D] #check (AlgebraicGeometry.Scheme.PseudoDivisor :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))

/- Remark 42.29.3 (2): an ambient Chow class with specified closed support can be intersected
with a pseudo-divisor, lowering degree by one and intersecting the two supports. -/
@[stacks 0B7D] #check (AlgebraicGeometry.Scheme.PseudoDivisor.intersectionSupported :
  ∀ {S X : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ S)
    [AlgebraicGeometry.UniversallyCatenary S] [AlgebraicGeometry.LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (D : AlgebraicGeometry.Scheme.PseudoDivisor X) (k : ℤ),
    AlgebraicGeometry.ChowGroup.Supported p δ (k + 1) →
      AlgebraicGeometry.ChowGroup.Supported p δ k)
