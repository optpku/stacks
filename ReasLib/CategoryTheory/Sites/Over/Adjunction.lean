/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Adjunctions on slice sites

For `f : X ⟶ Y`, postcomposition `Over.map f` is cocontinuous and its pullback right adjoint is
continuous as soon as pullbacks along `f` exist.  Consequently the inverse image on sheaves is
left adjoint both to the continuous direct-image presentation along `Over.pullback f` and to the
canonically isomorphic cocontinuous presentation along `Over.map f`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w t

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- Pullback on slice categories is continuous for the induced topologies whenever the required
pullbacks exist. -/
@[stacks 00XY "continuity of pullback on slice sites", instance]
instance overPullback_isContinuous (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    (Over.pullback f).IsContinuous (J.over Y) (J.over X) := sorry

/-- The continuous direct-image presentation on sheaves over slice sites. -/
@[stacks 00XY "direct image on slice sites"]
noncomputable abbrev overMapPushforward
    (J : GrothendieckTopology C) (A : Type w) [Category.{t} A]
    {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Sheaf (J.over X) A ⥤ Sheaf (J.over Y) A :=
  (Over.pullback f).sheafPushforwardContinuous A (J.over Y) (J.over X)

/-- The continuous and cocontinuous presentations of direct image on a slice site are canonically
isomorphic. -/
@[stacks 00XY "comparison of slice direct-image presentations"]
noncomputable def overMapPushforwardIsoCocontinuous
    (J : GrothendieckTopology C) (A : Type (w + 1)) [Category.{w} A]
    {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [∀ P : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension P] :
    J.overMapPushforward A f ≅
      (Over.map f).sheafPushforwardCocontinuous A (J.over X) (J.over Y) :=
  Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (Over.map f) (Over.pullback f) A (Over.mapPullbackAdj f)

/-- The inverse-image/continuous-direct-image adjunction on sheaves over slice sites. -/
@[stacks 00XY "slice inverse-image/direct-image adjunction"]
noncomputable def overMapPushforwardAdjunction
    (J : GrothendieckTopology C) (A : Type w) [Category.{t} A]
    {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    J.overMapPullback A f ⊣ J.overMapPushforward A f :=
  Adjunction.sheafPushforwardContinuous
    (Over.mapPullbackAdj f) (J.over X) (J.over Y)

/-- The inverse-image/cocontinuous-direct-image adjunction on sheaves over slice sites. -/
@[stacks 00XY "slice inverse-image/cocontinuous-direct-image adjunction"]
noncomputable def overMapCocontinuousAdjunction
    (J : GrothendieckTopology C) (A : Type (w + 1)) [Category.{w} A]
    {X Y : C} (f : X ⟶ Y)
    [∀ P : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension P] :
    J.overMapPullback A f ⊣
      (Over.map f).sheafPushforwardCocontinuous A (J.over X) (J.over Y) :=
  (Over.map f).sheafAdjunctionCocontinuous A (J.over X) (J.over Y)

end CategoryTheory.GrothendieckTopology
