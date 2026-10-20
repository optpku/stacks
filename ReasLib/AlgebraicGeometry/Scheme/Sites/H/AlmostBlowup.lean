module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.Affine
public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup

/-!
# Almost blowup squares and sheaves for the h topology

Sheaves of types for chosen big h-site slices and their affine subsites send
almost blowup squares to pullback squares.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigHSite.Sheaf

/-- A sheaf of types on a chosen big h-site slice sends a cartesian almost
blowup square to a pullback square of section types. -/
theorem map_isPullback_of_isAlmostBlowup
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : Sheaf (bigTopology Schh S) (Type w)) (sq : Square (Over S))
    [IsClosedImmersion ((ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄)]
    (h_pullback : (sq.map (ChosenBigSite.sliceToScheme Schh S)).IsPullback)
    (h_almostBlowup : IsAlmostBlowupSquare
      ((ChosenBigSite.sliceToScheme Schh S).map sq.f₂₄)
      ((ChosenBigSite.sliceToScheme Schh S).map sq.f₃₄).ker) :
    (sq.op.map F.obj).IsPullback := sorry

/-- A sheaf of types on the affine subsite of a chosen big h-site slice sends
a cartesian almost blowup square to a pullback square of section types. -/
theorem affineMap_isPullback_of_isAlmostBlowup
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (F : Sheaf (bigAffineTopology Schh S) (Type w))
    (sq : Square (ChosenBigSite.affineSite Schh S))
    [IsClosedImmersion ((ChosenBigSite.affineToScheme Schh S).map sq.f₃₄)]
    (h_pullback : (sq.map (ChosenBigSite.affineToScheme Schh S)).IsPullback)
    (h_almostBlowup : IsAlmostBlowupSquare
      ((ChosenBigSite.affineToScheme Schh S).map sq.f₂₄)
      ((ChosenBigSite.affineToScheme Schh S).map sq.f₃₄).ker) :
    (sq.op.map F.obj).IsPullback := sorry

end AlgebraicGeometry.ChosenBigHSite.Sheaf
