/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Point.FromSite
public import ReasLib.CategoryTheory.Sites.Topos.Point.CounitSplit
public import ReasLib.CategoryTheory.Sites.Topos.Point.Action
public import ReasLib.CategoryTheory.Sites.Action.SheafEquivalence

/-!
# Direct image of the forgetful action-site point

This module records the concrete `Type`-valued direct-image and counit formulas for the forgetful
point of the jointly-surjective action site.  The fiber formulas only need a monoid; the
right-translation `G`-set comparison additionally uses the sheaf equivalence for a group.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace Action

namespace ForgetfulPoint

noncomputable section

variable (G : Type u) [Monoid G]

/-- On the left regular action, the direct image of `S` agrees with the skyscraper presheaf of
the forgetful point. -/
noncomputable def pushforwardLeftRegularToSkyscraperEquiv (S : Type u) :
    ((forgetfulPoint G).toToposPoint.typePushforward.obj S).obj.obj
        (op (Action.leftRegular G)) ≃
      ((forgetfulPoint G).skyscraperPresheaf S).obj (op (Action.leftRegular G)) :=
  (((evaluation (Action (Type u) G)ᵒᵖ (Type u)).obj (op (Action.leftRegular G))).mapIso
    ((sheafToPresheaf (jointlySurjectiveTopology G) (Type u)).mapIso
      ((GrothendieckTopology.Point.toToposPoint_pointPushforwardIso
        (forgetfulPoint G)).app S))).toEquiv

/-- Evaluating the direct image of `S` on the left regular action gives the function type
`G → S`. -/
noncomputable def pushforwardLeftRegularEquiv (S : Type u) :
    ((forgetfulPoint G).toToposPoint.typePushforward.obj S).obj.obj
        (op (Action.leftRegular G)) ≃
      (G → S) :=
  (pushforwardLeftRegularToSkyscraperEquiv G S).trans
    (Types.productIso (fun _ : (forgetfulPoint G).fiber.obj (Action.leftRegular G) ↦ S)).toEquiv

/-- The canonical comparison from the inverse image of the direct image of `S` to `G → S`. -/
noncomputable def pushforwardFiberIso (S : Type u) :
    (forgetfulPoint G).toToposPoint.typeInverseImage.obj
      ((forgetfulPoint G).toToposPoint.typePushforward.obj S) ≅
      (G → S) :=
  ((GrothendieckTopology.Point.toToposPoint_pointInverseImageIso
      (forgetfulPoint G)).app ((forgetfulPoint G).toToposPoint.typePushforward.obj S)) ≪≫
    ((forgetfulPoint_sheafFiberIso_leftRegular G).app
      ((forgetfulPoint G).toToposPoint.typePushforward.obj S)) ≪≫
    (pushforwardLeftRegularEquiv G S).toIso

/-- Example 7.33.7 (00YF) (2): the inverse image of the direct image of `S` at the forgetful
point is canonically the function type `G → S`. -/
@[stacks 00YF "(2)"]
noncomputable def pushforwardFiberEquiv (S : Type u) :
    (forgetfulPoint G).toToposPoint.typeInverseImage.obj
      ((forgetfulPoint G).toToposPoint.typePushforward.obj S) ≃
      (G → S) :=
  (pushforwardFiberIso G S).toEquiv

/-- Example 7.33.7 (00YF) (4): under the canonical fiber equivalence, the section of the
direct-image counit is the constant-function map. -/
@[stacks 00YF "(4)"]
theorem pushforwardFiber_section_eq_const
    (S : Type u) :
    (fun s ↦
      pushforwardFiberEquiv G S
        ((forgetfulPoint G).toToposPoint.typeCounitSection.app S s)) =
      fun s _ ↦ s := sorry

/-- Example 7.33.7 (00YF) (5): under the canonical fiber equivalence, the direct-image
counit is evaluation at `1 ∈ G`. -/
@[stacks 00YF "(5)"]
theorem pushforwardFiber_counit_eq_eval_one
    (S : Type u) :
    (fun psi ↦
      ((forgetfulPoint G).toToposPoint.typeAdjunction.counit.app S)
        ((pushforwardFiberEquiv G S).symm psi)) =
      fun psi ↦ psi 1 := sorry

end

section

variable (G : Type u) [Group G]

/-- The left-regular-sections action commutes with the right-translation action on `G → S`. -/
theorem pushforward_rightTranslation_comm
    (S : Type u) (g : G) :
    ((CategoryTheory.Action.SheafEquivalence.LeftRegular.sectionsFunctor G).obj
        ((forgetfulPoint G).toToposPoint.typePushforward.obj S)).ρ g ≫
      (pushforwardLeftRegularEquiv G S).toIso.hom =
        (pushforwardLeftRegularEquiv G S).toIso.hom ≫
          (rightTranslationAction G S).ρ g := sorry

/-- Example 7.33.7 (00YF) (3): after identifying sheaves on the jointly-surjective action site
with `G`-sets by left-regular sections, the direct image of `S` is the right-translation action
on `G → S`. -/
@[stacks 00YF "(3)"]
noncomputable def pushforwardRightTranslationIso
    (S : Type u) :
    (CategoryTheory.Action.SheafEquivalence.LeftRegular.sectionsFunctor G).obj
        ((forgetfulPoint G).toToposPoint.typePushforward.obj S) ≅
      rightTranslationAction G S :=
  Action.mkIso
    (pushforwardLeftRegularEquiv G S).toIso
    (pushforward_rightTranslation_comm G S)

end

end ForgetfulPoint

end Action
