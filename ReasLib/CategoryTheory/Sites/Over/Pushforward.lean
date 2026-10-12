/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Continuity
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct image on slice sites

This leaf gives the canonical direct-image functor induced by a continuous
functor on a slice site and its compatibility with localization direct image.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- The direct image induced by `u : D ⥤ C` on the localized sites over `V`
and `u.obj V`.  The needed slice continuity is selected canonically from the
continuity of `u`, rather than exposed as an extra instance parameter. -/
@[stacks 03CF]
noncomputable def sheafPushforwardOverPost
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (A : Type uA) [Category.{vA} A] :
    Sheaf (JC.over (u.obj V)) A ⥤ Sheaf (JD.over V) A :=
  (Over.post u).sheafPushforwardContinuous A (JD.over V) (JC.over (u.obj V))

/-- Localization direct image commutes with the direct image induced by `u`. -/
@[stacks 03CF]
noncomputable def sheafPushforwardOverPostComp
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (A : Type uA) [Category.{vA} A] :
    JC.overPullback A (u.obj V) ⋙ sheafPushforwardOverPost u V A ≅
      u.sheafPushforwardContinuous A JD JC ⋙ JD.overPullback A V :=
  Functor.sheafPushforwardContinuousComp'
    (eqToIso (Over.post_forget_eq_forget_comp u V)) A
    (JD.over V) (JC.over (u.obj V)) JC

end CategoryTheory.Functor
