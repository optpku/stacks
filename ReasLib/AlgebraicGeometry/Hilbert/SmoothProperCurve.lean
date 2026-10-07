module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import ReasLib.AlgebraicGeometry.Hilbert.DivisorAddition
public import ReasLib.AlgebraicGeometry.Hilbert.Representability
public import ReasLib.AlgebraicGeometry.Hilbert.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Hilbert schemes of smooth proper curves

This file records representability and geometry of Hilbert schemes of points on smooth proper
geometrically irreducible curves, together with rational points and divisor addition.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/-- The degree-`d` Hilbert functor of a geometrically irreducible smooth proper curve over a
field is representable. -/
@[instance]
instance functor_isRepresentable_of_smoothProperCurve
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) : (functor X d).IsRepresentable := sorry

/-- The chosen degree-`d` Hilbert scheme of a geometrically irreducible smooth proper curve is
a proper variety. -/
@[instance]
instance representingScheme_properVariety
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) : ProperVariety (functor X d).reprX := sorry

/-- The chosen degree-`d` Hilbert scheme of a geometrically irreducible smooth proper curve is
a smooth proper variety of relative dimension `d` over the base field. -/
theorem representingScheme_smoothProperVariety
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d : ℕ) :
    SmoothOfRelativeDimension d (functor X d).reprX.hom ∧
      ProperVariety (functor X d).reprX := sorry

/-- Over a field extension `K/k`, the `K`-rational points of the degree-`d` Hilbert scheme
correspond to degree-`d` effective relative divisors on the base-changed curve. -/
def rationalPointsEquiv
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] (d : ℕ) :
    ((Over.mk (FieldExtension.specMap k K) : SchemeOverField k) ⟶ (functor X d).reprX) ≃
      Point X d (Over.mk (FieldExtension.specMap k K)) :=
  (functor X d).representableBy.homEquiv

/-- The rational-point equivalence is the canonical equivalence supplied by representability. -/
theorem rationalPointsEquiv_apply
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] (d : ℕ)
    (f : (Over.mk (FieldExtension.specMap k K) : SchemeOverField k) ⟶
      (functor X d).reprX) :
    rationalPointsEquiv X d f = (functor X d).representableBy.homEquiv f := sorry

/-- Addition of effective divisors of degrees `d₁` and `d₂` induces a finite locally free
morphism of rank `(d₁ + d₂).choose d₁` between their chosen Hilbert schemes. -/
@[instance]
instance additionMap_isFiniteLocallyFreeOfRank
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] (d₁ d₂ : ℕ) :
    IsFiniteLocallyFreeOfRank (additionMap X d₁ d₂).left ((d₁ + d₂).choose d₁) := sorry

end AlgebraicGeometry.Hilbert
