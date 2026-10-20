/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison.Left
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison.Braided
import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural pullback/internal-Hom comparison

@stack 08I3

An objectwise family `F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y` defines only pointwise internal-Hom
maps.  This leaf records the exact extra datum needed to assemble them into a two-variable natural
transformation: a natural isomorphism between the two tensor bifunctors.  Unit and associativity
coherence are deliberately not required.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor.PullbackInternalHom

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalCategory D] [BraidedCategory D]

namespace Bifunctor

/-- 08I3: A component of the natural pullback/internal-Hom comparison. -/
@[stacks 08I3 "natural pullback internal-Hom comparison component"]
noncomputable def comparisonApp
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) (X Y : C) :
    (sourceFunctor H F).obj (Opposite.op X, Y) ⟶
      (targetFunctor H' F).obj (Opposite.op X, Y) :=
  Functor.PullbackInternalHom.comparisonOf H H' F
    (fun A B ↦ T.app (A, B)) X Y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: The source-ordered comparison is the left-ordered comparison for the tensor comparison
conjugated by reverse braidings. -/
@[stacks 08I3 "source-ordered comparison as a reversed left comparison"]
theorem comparisonApp_eq_left_reverse
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) (X Y : C) :
    comparisonApp H H' F T X Y =
      Left.comparisonApp H H' F
        (TensorComparison.reverse F T) X Y := by
  change Functor.PullbackInternalHom.comparisonOf H H' F
      (fun A B ↦ T.app (A, B)) X Y =
    Left.comparisonOf H H' F (TensorComparison.reverse F T) X Y
  apply ((adjunctionOf H' (F.obj X)).homEquiv _ _).symm.injective
  rw [Left.comparisonOf_spec]
  rw [← cancel_epi (β_ (F.obj ((ihomOf H X).obj Y)) (F.obj X)).hom]
  calc
    _ = (braidedHomEquivOf H'
          (F.obj ((ihomOf H X).obj Y)) (F.obj X) (F.obj Y)).symm
        (Functor.PullbackInternalHom.comparisonOf H H' F
          (fun A B ↦ T.app (A, B)) X Y) :=
      (braidedHomEquivOf_symm_apply H' _).symm
    _ = Functor.PullbackInternalHom.evaluationOf H F
          (fun A B ↦ T.app (A, B)) X Y :=
      Functor.PullbackInternalHom.comparisonOf_spec H H' F
        (fun A B ↦ T.app (A, B)) X Y
    _ = _ := by
      simp [Functor.PullbackInternalHom.evaluationOf,
        TensorComparison.reverse, TensorComparison.reverseBraidingNatIso]
      rfl

/-- 08I3: Naturality of the pullback/internal-Hom comparison components.  The hypothesis `T` supplies
the naturality that an arbitrary objectwise family of tensor isomorphisms does not contain. -/
@[stacks 08I3 "natural pullback internal-Hom comparison"]
theorem comparisonApp_naturality
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    {P Q : Cᵒᵖ × C} (f : P ⟶ Q) :
    (sourceFunctor H F).map f ≫
        comparisonApp H H' F T Q.1.unop Q.2 =
      comparisonApp H H' F T P.1.unop P.2 ≫
        (targetFunctor H' F).map f := by
  rw [comparisonApp_eq_left_reverse, comparisonApp_eq_left_reverse]
  exact Left.comparisonApp_naturality H H' F
    (TensorComparison.reverse F T) f

/-- 08I3: The two-variable natural pullback/internal-Hom comparison. -/
@[stacks 08I3 "natural pullback internal-Hom comparison"]
noncomputable def comparison
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) :
    sourceFunctor H F ⟶ targetFunctor H' F where
  app P := comparisonApp H H' F T P.1.unop P.2
  naturality _ _ f := comparisonApp_naturality H H' F T f

/-- 08I3: The source-ordered natural comparison is the reversed left-ordered comparison. -/
@[stacks 08I3 "source-ordered natural comparison as a reversed left comparison"]
theorem comparison_eq_left_reverse
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) :
    comparison H H' F T =
      Left.comparison H H' F (TensorComparison.reverse F T) := by
  ext P
  rcases P with ⟨X, Y⟩
  exact comparisonApp_eq_left_reverse H H' F T X.unop Y

/-- 08I3: The explicit composite of two natural pullback/internal-Hom comparisons. -/
@[stacks 08I3 "composition of pullback internal-Hom comparisons"]
noncomputable def comparisonComp
    {E : Type uE} [Category.{vE} E]
    [MonoidalCategory E] [BraidedCategory E]
    (H : MonoidalClosed C) (H' : MonoidalClosed D) (H'' : MonoidalClosed E)
    (F : C ⥤ D) (G : D ⥤ E)
    (T : TensorComparison F) (U : TensorComparison G) :
    sourceFunctor H (F ⋙ G) ⟶ targetFunctor H'' (F ⋙ G) :=
  Functor.whiskerRight (comparison H H' F T) G ≫
    Functor.whiskerLeft (Functor.prod F.op F) (comparison H' H'' G U)

/-- 08I3: The comparison for a composite functor is the composite of the two comparisons. -/
@[stacks 08I3 "pullback internal-Hom comparison composition law"]
theorem comparison_comp
    {E : Type uE} [Category.{vE} E]
    [MonoidalCategory E] [BraidedCategory E]
    (H : MonoidalClosed C) (H' : MonoidalClosed D) (H'' : MonoidalClosed E)
    (F : C ⥤ D) (G : D ⥤ E)
    (T : TensorComparison F) (U : TensorComparison G) :
    comparison H H'' (F ⋙ G) (TensorComparison.comp F G T U) =
      comparisonComp H H' H'' F G T U := by
  rw [comparison_eq_left_reverse]
  rw [TensorComparison.reverse_comp]
  rw [Left.comparison_comp H H' H'' F G
    (TensorComparison.reverse F T) (TensorComparison.reverse G U)]
  unfold Left.comparisonComp comparisonComp
  rw [← comparison_eq_left_reverse H H' F T]
  rw [← comparison_eq_left_reverse H' H'' G U]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: The pullback/internal-Hom comparison for the identity functor is the identity. -/
@[stacks 08I3 "identity pullback internal-Hom comparison"]
theorem comparison_id (H : MonoidalClosed C) :
    comparison H H (𝟭 C) (TensorComparison.id C) = 𝟙 (internalHomFunctor H) := by
  ext P
  rcases P with ⟨X, Y⟩
  change Functor.PullbackInternalHom.comparisonOf H H (𝟭 C)
      (fun A B ↦ (TensorComparison.id C).app (A, B)) X.unop Y = 𝟙 _
  apply (braidedHomEquivOf H
    ((𝟭 C).obj ((ihomOf H X.unop).obj Y))
    ((𝟭 C).obj X.unop) ((𝟭 C).obj Y)).symm.injective
  rw [Functor.PullbackInternalHom.comparisonOf_spec]
  rw [braidedHomEquivOf_symm_apply]
  simp only [Functor.id_obj]
  rw [((@MonoidalClosed.internalHomAdjunction₂ C _ _ H).adj X.unop).homEquiv_symm_id Y]
  simp [Functor.PullbackInternalHom.evaluationOf, TensorComparison.id]

/-- 08I3: A component of the two-variable comparison is the pointwise pullback/internal-Hom map. -/
@[simp, stacks 08I3 "natural pullback internal-Hom comparison component"]
theorem comparison_app
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) (X Y : C) :
    (comparison H H' F T).app (Opposite.op X, Y) =
      Functor.PullbackInternalHom.comparisonOf H H' F
        (fun A B ↦ T.app (A, B)) X Y := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: Contravariant source naturality of the two-variable comparison. -/
@[reassoc, stacks 08I3 "pullback internal-Hom source naturality"]
theorem comparison_natural_source
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    {X₁ X₂ : C} (f : X₂ ⟶ X₁) (Y : C) :
    F.map ((preOf H f).app Y) ≫ comparisonApp H H' F T X₂ Y =
      comparisonApp H H' F T X₁ Y ≫
        (preOf H' (F.map f)).app (F.obj Y) := by
  have h := comparisonApp_naturality H H' F T
    (P := (Opposite.op X₁, Y)) (Q := (Opposite.op X₂, Y)) (f.op, 𝟙 Y)
  dsimp [sourceFunctor, targetFunctor, internalHomFunctor, Functor.uncurry,
    Functor.prod] at h ⊢
  simpa only [Functor.map_id, NatTrans.id_app, preOf_id_app, Category.id_comp,
    Category.comp_id] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: Covariant target naturality of the two-variable comparison. -/
@[reassoc, stacks 08I3 "pullback internal-Hom target naturality"]
theorem comparison_natural_target
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    F.map ((ihomOf H X).map f) ≫ comparisonApp H H' F T X Y₂ =
      comparisonApp H H' F T X Y₁ ≫
        (ihomOf H' (F.obj X)).map (F.map f) := by
  have hsource :
      (sourceFunctor H F).map
          (((𝟙 (Opposite.op X), f)) :
            (Opposite.op X, Y₁) ⟶ (Opposite.op X, Y₂)) =
        F.map ((ihomOf H X).map f) := by
    change F.map (internalHomMapOf H (𝟙 X) f) = _
    rw [internalHomMapOf_post]
  have htarget :
      (targetFunctor H' F).map
          (((𝟙 (Opposite.op X), f)) :
            (Opposite.op X, Y₁) ⟶ (Opposite.op X, Y₂)) =
        (ihomOf H' (F.obj X)).map (F.map f) := by
    change internalHomMapOf H' (F.map (𝟙 X)) (F.map f) = _
    rw [F.map_id, internalHomMapOf_post]
  have h := comparisonApp_naturality H H' F T
    (P := (Opposite.op X, Y₁)) (Q := (Opposite.op X, Y₂))
    (𝟙 (Opposite.op X), f)
  rw [hsource, htarget] at h
  exact h

end Bifunctor

end CategoryTheory.Functor.PullbackInternalHom
