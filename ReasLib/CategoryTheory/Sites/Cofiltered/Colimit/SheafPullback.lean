module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitTopology
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Sheaf pullback along a cofiltered colimit cocone

This leaf owns the coefficient-category-generic comparison between pullback
along a stage transition and pullback along the corresponding colimit cocone
functor.  It assumes only the three adjunction capabilities actually used by
the comparison; constructions from weak sheafification and Kan extensions
belong in higher capability owners.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uI uC vC w

namespace CategoryTheory

namespace CofilteredSiteDiagram

namespace ColimitPullback

/-- Pullback along a stage transition followed by pullback to the colimit site is canonically
the pullback along the source-stage cocone functor. -/
noncomputable def compIso
    {S : CofilteredSiteDiagram.{uI, uC, vC}}
    (A : Type w) [Category A]
    {i j : S.I} (a : j ⟶ i)
    [((S.stageFunctor a).sheafPushforwardContinuous A
      (S.stageTopology i) (S.stageTopology j)).IsRightAdjoint]
    [((S.stageCoconeFunctor j).sheafPushforwardContinuous A
      (S.stageTopology j) S.colimitTopology).IsRightAdjoint]
    [((S.stageCoconeFunctor i).sheafPushforwardContinuous A
      (S.stageTopology i) S.colimitTopology).IsRightAdjoint] :
    (S.stageFunctor a).sheafPullback A (S.stageTopology i) (S.stageTopology j) ⋙
        (S.stageCoconeFunctor j).sheafPullback A (S.stageTopology j) S.colimitTopology ≅
      (S.stageCoconeFunctor i).sheafPullback A (S.stageTopology i) S.colimitTopology :=
  Adjunction.leftAdjointCompIso
    ((S.stageFunctor a).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology j))
    ((S.stageCoconeFunctor j).sheafAdjunctionContinuous A
      (S.stageTopology j) S.colimitTopology)
    ((S.stageCoconeFunctor i).sheafAdjunctionContinuous A
      (S.stageTopology i) S.colimitTopology)
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (S.stageCoconeFunctor_comp_eq a))
      A (S.stageTopology i) (S.stageTopology j) S.colimitTopology)

end ColimitPullback

end CofilteredSiteDiagram

end CategoryTheory
