module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Separable
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.10.6: let `k` be a field, let `X` be a normal scheme over `k`, and
let `K / k` be a separable field extension. Then `X_K` is a normal scheme. -/
@[stacks 0C3M] #check
  (AlgebraicGeometry.SchemeOverField.isNormal_baseChange_of_isSeparableOver :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      [Algebra.IsSeparableOver k K]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.Scheme.isNormal X.left →
        AlgebraicGeometry.Scheme.isNormal
          (AlgebraicGeometry.FieldExtension.baseChange k K X.hom))
