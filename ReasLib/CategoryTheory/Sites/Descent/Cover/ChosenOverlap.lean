module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical

/-!
# Chosen overlaps of a Grothendieck cover

This module specializes the neutral chosen-pullback API to the arrows of a
Grothendieck cover.  The resulting short method-style names keep descent-data
clients independent of any particular chapter construction.
-/

@[expose] public section

noncomputable section

universe uC uD vC vD

namespace CategoryTheory.GrothendieckTopology.Cover

open CategoryTheory.Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {U : C}

/-- The canonical chosen pullback of two arrows in a cover. -/
noncomputable def chosenOverlap [HasPullbacks C]
    (T : J.Cover U) (I I' : T.Arrow) : ChosenPullback I.f I'.f :=
  ChosenPullback.ofHasPullback I.f I'.f

/-- The canonical chosen pullback of the two middle projections of three cover arrows. -/
noncomputable def chosenMiddleOverlap [HasPullbacks C]
    (T : J.Cover U) (I I' I'' : T.Arrow) :
    ChosenPullback (T.chosenOverlap I I').p₂ (T.chosenOverlap I' I'').p₁ :=
  ChosenPullback.ofHasPullback
    (T.chosenOverlap I I').p₂ (T.chosenOverlap I' I'').p₁

/-- Assemble the canonical pairwise and middle pullbacks into a threefold overlap using an
explicit outer lift. -/
def chosenTripleOverlap [HasPullbacks C]
    (T : J.Cover U) (I I' I'' : T.Arrow)
    (outerLift : ChosenPullback₃.MiddleLift
      (T.chosenOverlap I I') (T.chosenOverlap I' I'') (T.chosenOverlap I I'')
      (T.chosenMiddleOverlap I I' I'')) :
    ChosenPullback₃ (T.chosenOverlap I I') (T.chosenOverlap I' I'')
      (T.chosenOverlap I I'') :=
  ChosenPullback₃.ofMiddle
    (T.chosenOverlap I I') (T.chosenOverlap I' I'') (T.chosenOverlap I I'')
    (T.chosenMiddleOverlap I I' I'') outerLift

/-- The threefold chosen-overlap type for three cover arrows is nonempty. -/
theorem chosenTripleOverlapNonempty [HasPullbacks C]
    (T : J.Cover U) (I I' I'' : T.Arrow) :
    Nonempty
      (ChosenPullback₃ (T.chosenOverlap I I') (T.chosenOverlap I' I'')
        (T.chosenOverlap I I'')) := sorry

/-- The image chosen overlap of two cover arrows under a pullback-preserving functor. -/
noncomputable def imageChosenOverlap [HasPullbacks C]
    (T : J.Cover U) (u : C ⥤ D) [PreservesLimitsOfShape WalkingCospan u]
    (I I' : T.Arrow) : ChosenPullback (u.map I.f) (u.map I'.f) :=
  ChosenPullback.map u (T.chosenOverlap I I')

/-- The image chosen threefold overlap of cover arrows under a pullback-preserving functor. -/
noncomputable def imageChosenTripleOverlap [HasPullbacks C]
    (T : J.Cover U) (u : C ⥤ D) [PreservesLimitsOfShape WalkingCospan u]
    (I I' I'' : T.Arrow)
    (outerLift : ChosenPullback₃.MiddleLift
      (T.chosenOverlap I I') (T.chosenOverlap I' I'') (T.chosenOverlap I I'')
      (T.chosenMiddleOverlap I I' I'')) :
    ChosenPullback₃ (T.imageChosenOverlap u I I') (T.imageChosenOverlap u I' I'')
      (T.imageChosenOverlap u I I'') :=
  ChosenPullback₃.map u (T.chosenTripleOverlap I I' I'' outerLift)

end CategoryTheory.GrothendieckTopology.Cover
