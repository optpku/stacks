/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.UniversalDivisor
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

/- Remark 44.3.7 (1): the universal successor-degree divisor is relative effective Cartier. -/
@[stacks 0B9J] #check
  (AlgebraicGeometry.Hilbert.universalDivisor_isRelativeEffectiveCartier :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.GeometricallyIrreducible X.hom]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 X.hom] [AlgebraicGeometry.IsProper X.hom]
      (d : ℕ),
      AlgebraicGeometry.IsRelativeEffectiveCartierDivisor
        (CategoryTheory.Limits.pullback.snd X.hom
          (AlgebraicGeometry.Hilbert.functor X (d + 1)).reprX.hom)
        (AlgebraicGeometry.Hilbert.universalDivisor X (d + 1)))

/- Remark 44.3.7 (2): the universal divisor scheme is isomorphic to the degree-`d` product with the curve. -/
@[stacks 0B9J] #check
  (AlgebraicGeometry.Hilbert.universalDivisorSubscheme_isIsomorphic :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.GeometricallyIrreducible X.hom]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 X.hom] [AlgebraicGeometry.IsProper X.hom]
      (d : ℕ),
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.Hilbert.universalDivisor X (d + 1)).subscheme
        ((AlgebraicGeometry.Hilbert.functor X d).reprX ⊗ X).left)

/- Remark 44.3.7 (3): the universal successor-degree divisor is effective Cartier. -/
@[stacks 0B9J] #check
  (AlgebraicGeometry.Hilbert.universalDivisor_isEffectiveCartier :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.GeometricallyIrreducible X.hom]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 X.hom] [AlgebraicGeometry.IsProper X.hom]
      (d : ℕ),
      AlgebraicGeometry.IsEffectiveCartierDivisor
        (AlgebraicGeometry.Hilbert.universalDivisor X (d + 1)).subschemeι)

/- Remark 44.3.7 (4): the universal divisor sheaf is invertible. -/
@[stacks 0B9J] #check
  (AlgebraicGeometry.Hilbert.universalDivisorSheaf_isInvertible :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.GeometricallyIrreducible X.hom]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 X.hom] [AlgebraicGeometry.IsProper X.hom]
      (d : ℕ),
      AlgebraicGeometry.Scheme.Modules.Invertible
        (AlgebraicGeometry.Hilbert.universalDivisorSheaf X d))

/- Remark 44.3.7 (5): the fibre sheaf is associated to the ideal classified by the rational Hilbert point. -/
@[stacks 0B9J] #check
  (AlgebraicGeometry.Hilbert.universalDivisorFiber_isIsomorphic_classifiedSheaf :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.GeometricallyIrreducible X.hom]
      [AlgebraicGeometry.SmoothOfRelativeDimension 1 X.hom] [AlgebraicGeometry.IsProper X.hom]
      (d : ℕ)
      (x : (CategoryTheory.Over.mk
        (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k))) :
        AlgebraicGeometry.SchemeOverField k) ⟶
        (AlgebraicGeometry.Hilbert.functor X (d + 1)).reprX),
      CategoryTheory.IsIsomorphic
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Hilbert.fiberMap X x)).obj
          (AlgebraicGeometry.Hilbert.universalDivisorSheaf X d))
        (@AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf _
          ((AlgebraicGeometry.Hilbert.functor X (d + 1)).representableBy.homEquiv x).ideal
          ((AlgebraicGeometry.Hilbert.universalDivisor_fiber_ideal X d x) ▸
            (AlgebraicGeometry.Hilbert.universalDivisorFiber_isEffectiveCartier X d x))))
