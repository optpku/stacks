module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.PurelyInseparable

@[expose] public section

universe u

/- Lemma 33.10.2: for a scheme `X` over a field `k` and a point `x : X`, geometric normality at
`x`, normality of every stalk above `x` after a finite purely inseparable field extension, and
geometric normality of the stalk at `x` are equivalent.
-/
@[stacks 038N] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormalAt_tfae :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (x : X.left),
      List.TFAE
        [ AlgebraicGeometry.SchemeOverField.geometricallyNormalAt X x
        , ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
            [IsPurelyInseparable k K],
            ∀ x' : AlgebraicGeometry.FieldExtension.baseChange k K X.hom,
              AlgebraicGeometry.FieldExtension.toSource k K X.hom x' = x →
                IsNormalRing
                  ((AlgebraicGeometry.FieldExtension.baseChange k K X.hom).presheaf.stalk x')
        , Algebra.IsGeometricallyNormal k (X.left.presheaf.stalk x)
        ])
