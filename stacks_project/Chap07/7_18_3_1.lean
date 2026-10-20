module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitPullback

universe u

@[expose] public section

/- 7.18.3.1: in Situation 7.18.1, with u_i : C_i ⟶ C the cocone functor of
Lemma 7.18.2, for U_i in C_i and a sheaf F on C_i, the sheaf-pullback section
f_i⁻¹ F (u_i(U_i)) equals the filtered colimit of f_a⁻¹ F (u_a(U_i)) over
arrows a : j ⟶ i.

This is invertibility of ColimitPullback.comparison :
colimit (sectionDiagram S F X) ⟶
((stageCoconeFunctor i).sheafPullback (Type u) (stageTopology i)
colimitTopology).obj F evaluated at u_i(X). -/
@[stacks 09YM] #check
  (CategoryTheory.CofilteredSiteDiagram.ColimitPullback.comparison_isIso :
    ∀ (S : CategoryTheory.CofilteredSiteDiagram.{u, u, u}) {i : S.I}
      (F : CategoryTheory.Sheaf (S.stageTopology i) (Type u)) (X : S.stage i),
      CategoryTheory.IsIso
        (CategoryTheory.CofilteredSiteDiagram.ColimitPullback.comparison S F X))

#check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.comparison
#check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.sectionDiagram
#check @CategoryTheory.CofilteredSiteDiagram.ColimitPullback.comparison_bijective
