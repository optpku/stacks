module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalUnits.Basic

universe u

/- Lemma 33.28.3: For a connected reduced locally algebraic scheme with finitely
many irreducible components over an algebraically closed field, the quotient of
global units by scalar units is a finitely generated abelian group. -/
@[stacks 04L6] #check
  (AlgebraicGeometry.SchemeOverField.GlobalUnits.instModuleFiniteOfConnectedReduced :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsAlgClosed k]
      [ConnectedSpace X.left] [AlgebraicGeometry.IsReduced X.left]
      [AlgebraicGeometry.LocallyAlgebraic X] [Finite (irreducibleComponents X.left)],
      Module.Finite ℤ (Additive (AlgebraicGeometry.Scheme.Hom.unitsQuotient X.hom)))
