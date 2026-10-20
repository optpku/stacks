/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.SmoothProperCurve
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Hilbert

/- Proposition 44.3.6: the degree-`d` Hilbert functor of a geometrically irreducible smooth
proper curve over a field is representable. -/
@[stacks 0B9I] #check
  (AlgebraicGeometry.Hilbert.functor_isRepresentable_of_smoothProperCurve :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
      [IsProper X.hom] (d : ℕ), (functor X d).IsRepresentable)

/- The chosen degree-`d` representing scheme is a smooth proper variety of relative
dimension `d`. -/
#check
  (AlgebraicGeometry.Hilbert.representingScheme_smoothProperVariety :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
      [IsProper X.hom] (d : ℕ),
      SmoothOfRelativeDimension d (functor X d).reprX.hom ∧
        ProperVariety (functor X d).reprX)

/- Over every field extension `K/k`, rational points of the degree-`d` Hilbert scheme
correspond to degree-`d` effective divisors on the base-changed curve. -/
#check
  (AlgebraicGeometry.Hilbert.rationalPointsEquiv :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : SchemeOverField k) [Curve X] [GeometricallyIrreducible X.hom]
      [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] (d : ℕ),
      ((Over.mk (FieldExtension.specMap k K) : SchemeOverField k) ⟶ (functor X d).reprX) ≃
        Point X d (Over.mk (FieldExtension.specMap k K)))

/- Addition of effective divisors of degrees `d₁` and `d₂` is finite locally free of rank
`(d₁ + d₂).choose d₁`. -/
#check
  (AlgebraicGeometry.Hilbert.additionMap_isFiniteLocallyFreeOfRank :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [GeometricallyIrreducible X.hom] [SmoothOfRelativeDimension 1 X.hom]
      [IsProper X.hom] (d₁ d₂ : ℕ),
      IsFiniteLocallyFreeOfRank (additionMap X d₁ d₂).left ((d₁ + d₂).choose d₁))

end AlgebraicGeometry.Hilbert
