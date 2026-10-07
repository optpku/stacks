module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Automorphism

/-!
# Smooth positive-dimensional automorphism groups of genus 0 and 1 curves
-/

open AlgebraicGeometry CategoryTheory

universe u

/- Example 109.7.2 (Smooth positive dimensional automorphism group) (1): over an
algebraically closed field, a representing scheme of `autFunctor X` for a smooth
projective geometrically irreducible genus-zero curve `X` has topological Krull
dimension `3`. -/
@[stacks 0DSV] #check
  (AlgebraicGeometry.SchemeOverField.aut_topologicalKrullDim_eq_three_of_genus_zero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom],
      Curve.genus X = 0 → ∀ (G : SchemeOverField k),
      (SchemeOverField.autFunctor X ⋙ forget GrpCat).RepresentableBy G →
      topologicalKrullDim G.left = 3)

/- Example 109.7.2 (Smooth positive dimensional automorphism group) (2): over an
algebraically closed field, a representing scheme of `autFunctor X` for a smooth
projective geometrically irreducible genus-one curve `X` has topological Krull
dimension `1`. -/
@[stacks 0DSV] #check
  (AlgebraicGeometry.SchemeOverField.aut_topologicalKrullDim_eq_one_of_genus_one :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom],
      Curve.genus X = 1 → ∀ (G : SchemeOverField k),
      (SchemeOverField.autFunctor X ⋙ forget GrpCat).RepresentableBy G →
      topologicalKrullDim G.left = 1)
