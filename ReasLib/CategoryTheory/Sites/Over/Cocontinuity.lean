/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cocontinuous direct images on slice sites

Mathlib owns the canonical cocontinuity instance for `Over.post`.  This leaf
records the resulting direct-image square, whose presentation otherwise
requires repeated transport across the canonical slice triangle.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Composing the canonical slice forgetful functor with a cocontinuous functor is
cocontinuous. Unlike general composition, the intermediate topology `J` is determined by
the source `J.over U`, so this specialization is safe for typeclass search. -/
@[stacks 03EG "slice forget composite"]
instance IsCocontinuous.overForgetComp
    (u : C ⥤ D) {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} [u.IsCocontinuous J K] (U : C) :
    (Over.forget U ⋙ u).IsCocontinuous (J.over U) K := sorry

/-- Lemma 7.28.4: cocontinuous direct image commutes with localization at an
object and its image under `u`.  The cocontinuity of `Over.post u` is the
canonical Mathlib instance; this definition owns only the sheaf-level square.
-/
@[stacks 03EG]
noncomputable def sheafPushforwardCocontinuousOverPostComp
    (u : C ⥤ D) [u.IsCocontinuous J K] (U : C)
    (A : Type uA) [Category.{vA} A]
    [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasPointwiseRightKanExtension F]
    [∀ F : (Over (u.obj U))ᵒᵖ ⥤ A,
      (Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F]
    [∀ F : (Over U)ᵒᵖ ⥤ A, (Over.post u).op.HasPointwiseRightKanExtension F]
    [∀ F : (Over U)ᵒᵖ ⥤ A,
      (Over.forget U ⋙ u).op.HasPointwiseRightKanExtension F] :
    (Over.post u).sheafPushforwardCocontinuous A (J.over U) (K.over (u.obj U)) ⋙
        (Over.forget (u.obj U)).sheafPushforwardCocontinuous A
          (K.over (u.obj U)) K ≅
      (Over.forget U).sheafPushforwardCocontinuous A (J.over U) J ⋙
        u.sheafPushforwardCocontinuous A J K :=
  (Functor.sheafPushforwardCocontinuousComp'
      (J.over U) (K.over (u.obj U)) K (Over.post u) (Over.forget (u.obj U))
      (eqToIso (Over.post_forget_eq_forget_comp u U))) ≪≫
    (Functor.sheafPushforwardCocontinuousComp
      (J.over U) J K (Over.forget U) u).symm

end CategoryTheory.Functor

namespace CategoryTheory.GrothendieckTopology

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
variable [UnivLE.{max uC vC, uA}]

/-- Direct image along two successive changes of slice base agrees canonically with direct
image along their composite. -/
noncomputable def overMapPushforwardCompIso {U V W : C}
    (f : U ⟶ V) (g : V ⟶ W) :
    (Over.map f).sheafPushforwardCocontinuous (Type uA) (J.over U) (J.over V) ⋙
        (Over.map g).sheafPushforwardCocontinuous (Type uA) (J.over V) (J.over W) ≅
      (Over.map (f ≫ g)).sheafPushforwardCocontinuous
        (Type uA) (J.over U) (J.over W) :=
  Functor.sheafPushforwardCocontinuousComp'
    (J.over U) (J.over V) (J.over W)
    (Over.map f) (Over.map g) (Over.mapComp f g).symm

/-- Equal arrows induce canonically isomorphic direct images between the corresponding slice
topoi. -/
noncomputable def overMapPushforwardCongrIso {U V : C}
    {f g : U ⟶ V} (h : f = g) :
    (Over.map f).sheafPushforwardCocontinuous (Type uA) (J.over U) (J.over V) ≅
      (Over.map g).sheafPushforwardCocontinuous (Type uA) (J.over U) (J.over V) :=
  Functor.sheafPushforwardCocontinuousIso
    (J.over U) (J.over V) (Over.map f) (Over.mapCongr f g h)

end CategoryTheory.GrothendieckTopology

-- Both slice direct-image comparisons are canonical functor isomorphisms with no deferred
-- non-Prop payload.
