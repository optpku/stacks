/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.FunctionField
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.6.8 (1): geometric reducedness at a point is preserved under generization. -/
@[stacks 04KS]
#check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt_of_specializes :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      {x x' : X.left},
      Specializes x' x →
        AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x →
          AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x')

/- Lemma 33.6.8 (2): a reduced stalk is geometrically reduced if the scheme is geometrically
reduced at every component-generic point specializing to it. -/
@[stacks 04KS]
#check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt.of_isReduced_stalk_of_genericPoints :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) (x : X.left),
      _root_.IsReduced (X.left.presheaf.stalk x) →
        (∀ x' : X.left,
          x' ∈ genericPoints X.left →
            Specializes x' x →
              AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x') →
          AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x)

/- Lemma 33.6.8 (3): a reduced scheme geometrically reduced at all component-generic points is
geometrically reduced. -/
@[stacks 04KS]
#check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced.of_isReduced_of_genericPoints :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.IsReduced X.left],
      (∀ x : X.left,
        x ∈ genericPoints X.left →
          AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x) →
        AlgebraicGeometry.SchemeOverField.geometricallyReduced X)

/- Lemma 33.6.8 (4): a variety is geometrically reduced exactly when its function field is
separable over the base field. -/
@[stacks 04KS]
#check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced_iff_functionField_isSeparableOver :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Variety X],
      AlgebraicGeometry.SchemeOverField.geometricallyReduced X ↔
        AlgebraicGeometry.SchemeOverField.functionFieldIsSeparableOver X)
