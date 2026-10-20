module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.AlmostBlowup
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Lemma 38.37.7 (1): a sheaf on the chosen big h site sends an almost blowup
square to a pullback square of types. -/
@[stacks 0EVD] #check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.map_isPullback_of_isAlmostBlowup :
    ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : Schh.carrier)
      (F : Sheaf (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S) (Type w))
      (sq : Square (Over S))
      [h_closed : AlgebraicGeometry.IsClosedImmersion
        ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄)],
      (sq.map (AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S)).IsPullback →
      AlgebraicGeometry.IsAlmostBlowupSquare
        ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).map sq.f₂₄)
        ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄).ker →
      (sq.op.map F.obj).IsPullback)

/- Lemma 38.37.7 (2): a sheaf on the affine chosen big h site sends an almost
blowup square to a pullback square of types. -/
@[stacks 0EVD] #check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.affineMap_isPullback_of_isAlmostBlowup :
    ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : Schh.carrier)
      (F : Sheaf (AlgebraicGeometry.ChosenBigHSite.bigAffineTopology Schh S) (Type w))
      (sq : Square (AlgebraicGeometry.ChosenBigSite.affineSite Schh S))
      [h_closed : AlgebraicGeometry.IsClosedImmersion
        ((AlgebraicGeometry.ChosenBigSite.affineToScheme Schh S).map sq.f₃₄)],
      (sq.map (AlgebraicGeometry.ChosenBigSite.affineToScheme Schh S)).IsPullback →
      AlgebraicGeometry.IsAlmostBlowupSquare
        ((AlgebraicGeometry.ChosenBigSite.affineToScheme Schh S).map sq.f₂₄)
        ((AlgebraicGeometry.ChosenBigSite.affineToScheme Schh S).map sq.f₃₄).ker →
      (sq.op.map F.obj).IsPullback)
