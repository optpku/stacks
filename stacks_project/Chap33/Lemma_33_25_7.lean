module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.SmoothLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.25.7: let `X` be a reduced scheme that is locally of finite type over a field `k`.
Then `X` is geometrically reduced over `k` if and only if `X` contains a dense open subscheme
that is smooth over `k`. -/
@[stacks 056V] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced_iff_exists_dense_open_smooth :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] [IsReduced X.left],
      AlgebraicGeometry.SchemeOverField.geometricallyReduced X ↔
        ∃ U : X.left.Opens, Dense (U : Set X.left) ∧ Smooth (U.ι ≫ X.hom))
