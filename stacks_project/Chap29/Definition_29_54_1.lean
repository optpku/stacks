module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]

#check (AlgebraicGeometry.Scheme.normalization X : AlgebraicGeometry.Scheme.{u})

/- Definition 29.54.1: the normalization morphism from the normalization of `X` in the
generic-point residue-field coproduct map to `X`. -/
@[stacks 035N] #check
  (AlgebraicGeometry.Scheme.normalizationTo X :
    AlgebraicGeometry.Scheme.normalization X ⟶ X)

#check
  (AlgebraicGeometry.Scheme.normalization_eq X :
    AlgebraicGeometry.Scheme.normalization X =
      (AlgebraicGeometry.genericPointSpectrumCoproductTo X).normalization)

#check
  (AlgebraicGeometry.Scheme.normalizationTo_eq X :
    AlgebraicGeometry.Scheme.normalizationTo X =
      (AlgebraicGeometry.genericPointSpectrumCoproductTo X).fromNormalization)
