module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Pushout
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
universe u

/- Lemma 99.15.7: restriction of families of curves along a pushout with a
thickening and an affine map is an equivalence of fibre categories. -/
@[stacks 0D56] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.restrictionComparison.instIsEquivalence :
    ∀ {B : Scheme.{u}} {T T' S S' : Over B}
      {i : T ⟶ T'} {f : T ⟶ S} {inl : T' ⟶ S'} {inr : S ⟶ S'}
      [IsThickening i.left] [IsAffineHom f.left] (h : IsPushout i f inl inr),
      (Functor.restrictionComparison
        (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p B) h.w).IsEquivalence)
