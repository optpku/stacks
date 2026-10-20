module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal

/-!
# Definition 33.10.1 (038M): geometric normality

The canonical pointwise and global owners are in
`AlgebraicGeometry.SchemeOverField`.
-/

universe u

/- Definition 33.10.1: a scheme over a field is geometrically normal at a point when every local
ring above that point after every field extension is normal. -/
@[stacks 038M] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormalAt_iff :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (x : X.left),
      AlgebraicGeometry.SchemeOverField.geometricallyNormalAt X x ↔
        ∀ (K : Type u) [Field K] [Algebra k K],
          ∀ x' : AlgebraicGeometry.FieldExtension.baseChange k K X.hom,
            AlgebraicGeometry.FieldExtension.toSource k K X.hom x' = x →
              IsNormalRing
                ((AlgebraicGeometry.FieldExtension.baseChange k K X.hom).presheaf.stalk x'))

/- A scheme over a field is geometrically normal when it is geometrically normal at every point. -/
#check
  (AlgebraicGeometry.SchemeOverField.geometricallyNormal_iff :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.SchemeOverField.geometricallyNormal X ↔
        ∀ x : X.left, AlgebraicGeometry.SchemeOverField.geometricallyNormalAt X x)
