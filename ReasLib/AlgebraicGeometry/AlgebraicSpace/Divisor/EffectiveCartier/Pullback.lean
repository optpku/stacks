module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Pullbacks of effective Cartier divisors on algebraic spaces

The inverse image of an effective Cartier divisor is effective Cartier if all
weakly associated points map outside the divisor, or if the morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The pullback of an effective Cartier divisor along a morphism is defined
when its inverse-image closed subspace is an effective Cartier divisor. -/
def ClosedSubspace.IsPullbackDefined
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] (f : Y ⟶ X) : Prop :=
  IsEffectiveCartierDivisor (D.inverseImageSubspace f).ι

/-- Pullback-definedness is equivalent to the inverse-image closed subspace
being an effective Cartier divisor. -/
theorem ClosedSubspace.isPullbackDefined_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] (f : Y ⟶ X) :
    D.IsPullbackDefined f ↔ IsEffectiveCartierDivisor (D.inverseImageSubspace f).ι :=
  Iff.rfl

/-- If every weakly associated point of the source maps outside an effective
Cartier divisor, its inverse image is an effective Cartier divisor. -/
theorem pullbackDefined_of_weakAss_outside_support
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    (hweak : ∀ x : Points X', x ∈ X'.weakAss → Points.map f x ∉ D.pointsSet) :
    IsEffectiveCartierDivisor (D.inverseImageSubspace f).ι :=
  sorry

/-- The inverse image of an effective Cartier divisor along a flat morphism
of algebraic spaces is an effective Cartier divisor. -/
theorem pullbackDefined_of_flat
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [Flat f]
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    IsEffectiveCartierDivisor (D.inverseImageSubspace f).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
