module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalUnits.BaseField

universe u

/- Lemma 33.28.6: Let `k` be a field and `X` a variety over `k`. If `k` is integrally closed
in the global sections of `X`, if `k` is algebraically closed in the function field of `X`, if
`X` is geometrically integral over `k`, or if `k` is the intersection of the residue fields of
the closed points of `X`, then the global units of `X` modulo scalar units form a finitely
generated abelian group.
-/
@[stacks 04L8] #check
  (AlgebraicGeometry.SchemeOverField.GlobalUnits.moduleFinite_of_varietyBaseFieldCondition :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Variety X],
      (AlgebraicGeometry.SchemeOverField.BaseField.GlobalSections.isIntegrallyClosed X ∨
        AlgebraicGeometry.SchemeOverField.BaseField.FunctionField.isAlgebraicallyClosed X ∨
        AlgebraicGeometry.GeometricallyIntegral X.hom ∨
        AlgebraicGeometry.SchemeOverField.BaseField.ClosedPointResidues.intersection_eq_base X) →
      Module.Finite ℤ (Additive (AlgebraicGeometry.Scheme.Hom.unitsQuotient X.hom)))
