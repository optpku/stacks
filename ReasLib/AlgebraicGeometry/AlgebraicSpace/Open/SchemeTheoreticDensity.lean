module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Open

variable {S : Scheme.{u}} {Y V : AlgebraicSpace S}

/-- An open subspace is scheme-theoretically dense if its pullback to every étale scheme
chart, in every scheme representation of that pullback, is scheme-theoretically dominant. -/
def IsSchemeTheoreticallyDense (ι : V ⟶ Y) : Prop :=
  ∀ (U : SmallEtale.site Y) (W : Over S) (map : W ⟶ U.left)
    (toOpen : yoneda.obj W ⟶ V.functorOfPoints),
    IsPullback toOpen (yoneda.map map) (ι : V.functorOfPoints ⟶ Y.functorOfPoints) U.hom →
      AlgebraicGeometry.IsSchemeTheoreticallyDominant map.left

/-- Scheme-theoretic density is equivalent to scheme-theoretic dominance in each genuine
scheme pullback along an étale chart. -/
theorem isSchemeTheoreticallyDense_iff (ι : V ⟶ Y) :
    IsSchemeTheoreticallyDense ι ↔
      ∀ (U : SmallEtale.site Y) (W : Over S) (map : W ⟶ U.left)
        (toOpen : yoneda.obj W ⟶ V.functorOfPoints),
        IsPullback toOpen (yoneda.map map) (ι : V.functorOfPoints ⟶ Y.functorOfPoints) U.hom →
          AlgebraicGeometry.IsSchemeTheoreticallyDominant map.left := sorry

end AlgebraicGeometry.AlgebraicSpace.Open
