/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pullback
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- Direct image of abelian sheaves on the small Zariski sites of schemes. -/
def zariskiAbelianPushforward {X' X : Scheme.{u}} (f : X' ⟶ X) :
    Sheaf X'.smallZariskiTopology AddCommGrpCat.{v} ⥤
      Sheaf X.smallZariskiTopology AddCommGrpCat.{v} :=
  (smallZariskiPullback f).sheafPushforwardContinuous AddCommGrpCat.{v}
    X.smallZariskiTopology X'.smallZariskiTopology

/-- Zariski direct image of abelian sheaves is additive. -/
instance zariskiAbelianPushforward_additive {X' X : Scheme.{u}} (f : X' ⟶ X) :
    (zariskiAbelianPushforward.{u, v} f).Additive := sorry

/-- Direct image along a homeomorphism of schemes preserves finite colimits of
abelian Zariski sheaves. -/
theorem zariskiAbelianPushforward_preservesFiniteColimits_of_isHomeomorph
    {X' X : Scheme.{u}} (f : X' ⟶ X) (hf : IsHomeomorph f) :
    PreservesFiniteColimits (zariskiAbelianPushforward.{u, v} f) := sorry

/-- A homeomorphism of schemes induces an exact direct-image functor on abelian
Zariski sheaves. -/
def zariskiAbelianPushforwardExact {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hf : IsHomeomorph f) :
    Sheaf X'.smallZariskiTopology AddCommGrpCat.{v} ⥤ₑ
      Sheaf X.smallZariskiTopology AddCommGrpCat.{v} :=
  let F := zariskiAbelianPushforward.{u, v} f
  let G := sheafToPresheaf X.smallZariskiTopology AddCommGrpCat.{v}
  let e := (smallZariskiPullback f).sheafPushforwardContinuousCompSheafToPresheafIso
    AddCommGrpCat.{v} X.smallZariskiTopology X'.smallZariskiTopology
  let hComp : PreservesFiniteLimits (F ⋙ G) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ e.symm
      (comp_preservesFiniteLimits
        (sheafToPresheaf X'.smallZariskiTopology AddCommGrpCat.{v})
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (smallZariskiPullback f).op))
  ⟨F, ⟨@preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _ F G hComp
    inferInstance, zariskiAbelianPushforward_preservesFiniteColimits_of_isHomeomorph f hf⟩⟩

end AlgebraicGeometry.Scheme
