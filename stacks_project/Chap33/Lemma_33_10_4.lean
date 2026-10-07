module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.10.4 (1): geometric normality at a point is preserved and reflected
at every specified point above it after extending the ground field. -/
@[stacks 038P] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormalAt_iff_of_baseChange :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (x : X.left)
      (x' : (AlgebraicGeometry.FieldExtension.Over.baseChange k k' X).left),
      AlgebraicGeometry.FieldExtension.Over.toSource k k' X x' = x →
        (AlgebraicGeometry.SchemeOverField.geometricallyNormalAt X x ↔
          AlgebraicGeometry.SchemeOverField.geometricallyNormalAt
            (AlgebraicGeometry.FieldExtension.Over.baseChange k k' X) x'))

/- Lemma 33.10.4 (2): geometric normality of a scheme over a field is preserved
and reflected after extending the ground field. -/
@[stacks 038P] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormal_iff_baseChange :
    ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.SchemeOverField.geometricallyNormal X ↔
        AlgebraicGeometry.SchemeOverField.geometricallyNormal
          (AlgebraicGeometry.FieldExtension.Over.baseChange k k' X))
