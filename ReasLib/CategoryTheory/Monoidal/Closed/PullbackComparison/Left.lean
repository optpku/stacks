module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Braiding-free natural pullback/internal-Hom comparison

@stack 08I3

A natural tensor comparison produces a two-variable internal-Hom comparison using the ordinary
left tensor/internal-Hom adjunction. No braiding is required.
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
variable [MonoidalCategory C] [MonoidalCategory D]

namespace Bifunctor

/-- 08I3: The uncurried internal-Hom bifunctor selected by an explicit closed structure. -/
@[stacks 08I3 "explicit internal-Hom bifunctor"]
noncomputable abbrev internalHomFunctor
    (H : MonoidalClosed C) : Cᵒᵖ × C ⥤ C :=
  Functor.uncurry.obj (internalHomOf H)

/-- 08I3: The source bifunctor for the natural pullback/internal-Hom comparison. -/
@[stacks 08I3 "pullback internal-Hom source bifunctor"]
noncomputable abbrev sourceFunctor
    (H : MonoidalClosed C) (F : C ⥤ D) : Cᵒᵖ × C ⥤ D :=
  internalHomFunctor H ⋙ F

/-- 08I3: The target bifunctor for the natural pullback/internal-Hom comparison. -/
@[stacks 08I3 "pullback internal-Hom target bifunctor"]
noncomputable abbrev targetFunctor
    (H : MonoidalClosed D) (F : C ⥤ D) : Cᵒᵖ × C ⥤ D :=
  Functor.prod F.op F ⋙ internalHomFunctor H

end Bifunctor

namespace Left

/-!
The left-ordered view keeps `F.obj X ⊗ F.obj [X, Y]` on the target side.  It is the
braiding-free comparison; the `Bifunctor` view above intentionally retains its source-order
orientation for compatibility with the generic pullback owner.
-/

/-- 08I3: The source bifunctor for the braiding-free left-ordered comparison. -/
@[stacks 08I3 "left-ordered pullback internal-Hom source bifunctor"]
noncomputable abbrev sourceFunctor
    (H : MonoidalClosed C) (F : C ⥤ D) : Cᵒᵖ × C ⥤ D :=
  Bifunctor.sourceFunctor H F

/-- 08I3: The target bifunctor for the braiding-free left-ordered comparison. -/
@[stacks 08I3 "left-ordered pullback internal-Hom target bifunctor"]
noncomputable abbrev targetFunctor
    (H : MonoidalClosed D) (F : C ⥤ D) : Cᵒᵖ × C ⥤ D :=
  Bifunctor.targetFunctor H F

/-- 08I3: A left-ordered pullback/internal-Hom comparison component from an explicit tensor
comparison. -/
@[stacks 08I3 "left-ordered pullback internal-Hom comparison component"]
noncomputable def comparisonOf
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) (X Y : C) :
    F.obj ((MonoidalClosed.ihomOf H X).obj Y) ⟶
      (MonoidalClosed.ihomOf H' (F.obj X)).obj (F.obj Y) :=
  (MonoidalClosed.adjunctionOf H' (F.obj X)).homEquiv _ _
    (T.inv.app (X, (MonoidalClosed.ihomOf H X).obj Y) ≫
      F.map ((MonoidalClosed.adjunctionOf H X).counit.app Y))

/-- 08I3: The left-ordered comparison transposes to the tensor comparison followed by evaluation. -/
@[stacks 08I3 "left-ordered pullback internal-Hom comparison specification"]
theorem comparisonOf_spec
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) (X Y : C) :
    ((MonoidalClosed.adjunctionOf H' (F.obj X)).homEquiv _ _).symm
        (comparisonOf H H' F T X Y) =
      T.inv.app (X, (MonoidalClosed.ihomOf H X).obj Y) ≫
        F.map ((MonoidalClosed.adjunctionOf H X).counit.app Y) :=
  Equiv.symm_apply_apply _ _

/-- 08I3: The left-ordered pullback/internal-Hom comparison component as a named app surface. -/
@[stacks 08I3 "left-ordered pullback internal-Hom comparison app"]
noncomputable abbrev comparisonApp
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) (X Y : C) :
    (sourceFunctor H F).obj (Opposite.op X, Y) ⟶
      (targetFunctor H' F).obj (Opposite.op X, Y) :=
  comparisonOf H H' F T X Y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comparisonApp_natural_source_aux
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    {X₁ X₂ : C} (f : X₂ ⟶ X₁) (Y : C) :
    F.map ((preOf H f).app Y) ≫ comparisonApp H H' F T X₂ Y =
      comparisonApp H H' F T X₁ Y ≫
        (preOf H' (F.map f)).app (F.obj Y) := by
  change F.map ((preOf H f).app Y) ≫ comparisonOf H H' F T X₂ Y =
    comparisonOf H H' F T X₁ Y ≫
      (preOf H' (F.map f)).app (F.obj Y)
  apply ((adjunctionOf H' (F.obj X₂)).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [comparisonOf_spec]
  change _ = (adj₂Of H').homEquiv.symm
    (comparisonOf H H' F T X₁ Y ≫
      ((internalHomOf H').map (F.map f).op).app (F.obj Y))
  rw [(adj₂Of H').homEquiv_symm_naturality_one
    (F.map f) (comparisonOf H H' F T X₁ Y)]
  have hspec :
      (adj₂Of H').homEquiv.symm (comparisonOf H H' F T X₁ Y) =
        T.inv.app (X₁, (ihomOf H X₁).obj Y) ≫
          F.map ((adjunctionOf H X₁).counit.app Y) := by
    exact comparisonOf_spec H H' F T X₁ Y
  rw [hspec]
  have hTpre :
      (tensorLeft (F.obj X₂)).map (F.map ((preOf H f).app Y)) ≫
          T.inv.app (X₂, (ihomOf H X₂).obj Y) =
        T.inv.app (X₂, (ihomOf H X₁).obj Y) ≫
          F.map ((tensorLeft X₂).map ((preOf H f).app Y)) := by
    simpa [Functor.tensorFunctor] using
      T.inv.naturality
        (((𝟙 X₂, (preOf H f).app Y)) :
          (X₂, (ihomOf H X₁).obj Y) ⟶ (X₂, (ihomOf H X₂).obj Y))
  rw [← Category.assoc, hTpre]
  have hTf :
      ((curriedTensor D).map (F.map f)).app (F.obj ((ihomOf H X₁).obj Y)) ≫
          T.inv.app (X₁, (ihomOf H X₁).obj Y) =
        T.inv.app (X₂, (ihomOf H X₁).obj Y) ≫
          F.map (((curriedTensor C).map f).app ((ihomOf H X₁).obj Y)) := by
    simpa [Functor.tensorFunctor] using
      T.inv.naturality
        (((f, 𝟙 ((ihomOf H X₁).obj Y))) :
          (X₂, (ihomOf H X₁).obj Y) ⟶ (X₁, (ihomOf H X₁).obj Y))
  have hcounit :
      F.map ((tensorLeft X₂).map ((preOf H f).app Y)) ≫
          F.map ((adjunctionOf H X₂).counit.app Y) =
        F.map (((curriedTensor C).map f).app ((ihomOf H X₁).obj Y)) ≫
          F.map ((adjunctionOf H X₁).counit.app Y) := by
    simpa [TensorInternalHom.counitOf, Functor.map_comp] using
      congrArg F.map (TensorInternalHom.counitOf_natural_source H f Y).symm
  rw [Category.assoc, hcounit]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ F.map ((adjunctionOf H X₁).counit.app Y)) hTf.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comparisonApp_natural_target_aux
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    F.map ((ihomOf H X).map f) ≫ comparisonApp H H' F T X Y₂ =
      comparisonApp H H' F T X Y₁ ≫
        (ihomOf H' (F.obj X)).map (F.map f) := by
  change F.map ((ihomOf H X).map f) ≫ comparisonOf H H' F T X Y₂ =
    comparisonOf H H' F T X Y₁ ≫
      (ihomOf H' (F.obj X)).map (F.map f)
  apply ((adjunctionOf H' (F.obj X)).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [comparisonOf_spec]
  rw [Adjunction.homEquiv_naturality_right_symm]
  rw [comparisonOf_spec]
  have hTmap :
      (tensorLeft (F.obj X)).map (F.map ((ihomOf H X).map f)) ≫
          T.inv.app (X, (ihomOf H X).obj Y₂) =
        T.inv.app (X, (ihomOf H X).obj Y₁) ≫
          F.map ((tensorLeft X).map ((ihomOf H X).map f)) := by
    simpa [Functor.tensorFunctor] using
      T.inv.naturality
        (((𝟙 X, (ihomOf H X).map f)) :
          (X, (ihomOf H X).obj Y₁) ⟶ (X, (ihomOf H X).obj Y₂))
  rw [← Category.assoc, hTmap]
  have hcounit :
      F.map ((tensorLeft X).map ((ihomOf H X).map f)) ≫
          F.map ((adjunctionOf H X).counit.app Y₂) =
        F.map ((adjunctionOf H X).counit.app Y₁) ≫ F.map f := by
    simpa [TensorInternalHom.counitOf, Functor.map_comp] using
      congrArg F.map (TensorInternalHom.counitOf_natural_target H X f)
  rw [Category.assoc, hcounit]
  simp only [Category.assoc]

/-- 08I3: Naturality of the left-ordered comparison in the two-variable source product. -/
@[stacks 08I3 "left-ordered pullback internal-Hom comparison naturality"]
theorem comparisonApp_naturality
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    {P Q : Cᵒᵖ × C} (f : P ⟶ Q) :
    (sourceFunctor H F).map f ≫
        comparisonApp H H' F T Q.1.unop Q.2 =
      comparisonApp H H' F T P.1.unop P.2 ≫
        (targetFunctor H' F).map f := by
  rcases P with ⟨X₁, Y₁⟩
  rcases Q with ⟨X₂, Y₂⟩
  rcases f with ⟨fX, fY⟩
  dsimp only at fX fY
  change F.map (internalHomMapOf H fX.unop fY) ≫
      comparisonOf H H' F T X₂.unop Y₂ =
    comparisonOf H H' F T X₁.unop Y₁ ≫
      internalHomMapOf H' (F.map fX.unop) (F.map fY)
  rw [internalHomMapOf, F.map_comp, Category.assoc]
  change F.map ((preOf H fX.unop).app Y₁) ≫
      (F.map ((ihomOf H X₂.unop).map fY) ≫
        comparisonApp H H' F T X₂.unop Y₂) =
    comparisonApp H H' F T X₁.unop Y₁ ≫
      ((preOf H' (F.map fX.unop)).app (F.obj Y₁) ≫
        (ihomOf H' (F.obj X₂.unop)).map (F.map fY))
  rw [comparisonApp_natural_target_aux]
  let post := (ihomOf H' (F.obj X₂.unop)).map (F.map fY)
  have hs := comparisonApp_natural_source_aux H H' F T fX.unop Y₁
  calc
    _ = (F.map ((preOf H fX.unop).app Y₁) ≫
          comparisonApp H H' F T X₂.unop Y₁) ≫ post :=
      (Category.assoc _ _ _).symm
    _ = (comparisonApp H H' F T X₁.unop Y₁ ≫
          (preOf H' (F.map fX.unop)).app (F.obj Y₁)) ≫ post :=
      congrArg (fun k => k ≫ post) hs
    _ = _ := Category.assoc _ _ _

/-- 08I3: The left-ordered two-variable pullback/internal-Hom comparison. -/
@[stacks 08I3 "left-ordered pullback internal-Hom comparison"]
noncomputable def comparison
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) :
    sourceFunctor H F ⟶ targetFunctor H' F where
  app P := comparisonApp H H' F T P.1.unop P.2
  naturality _ _ f := comparisonApp_naturality H H' F T f

/-- 08I3: A component of the left-ordered two-variable comparison. -/
@[simp, stacks 08I3 "left-ordered pullback internal-Hom comparison app formula"]
theorem comparison_app
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F) (X Y : C) :
    (comparison H H' F T).app (Opposite.op X, Y) =
      comparisonApp H H' F T X Y := rfl

/-- 08I3: The explicit composite of two braiding-free left-ordered comparisons. -/
@[stacks 08I3 "composition of left-ordered pullback internal-Hom comparisons"]
noncomputable def comparisonComp
    {E : Type uE} [Category.{vE} E] [MonoidalCategory E]
    (H : MonoidalClosed C) (H' : MonoidalClosed D) (H'' : MonoidalClosed E)
    (F : C ⥤ D) (G : D ⥤ E)
    (T : TensorComparison F) (U : TensorComparison G) :
    sourceFunctor H (F ⋙ G) ⟶ targetFunctor H'' (F ⋙ G) :=
  Functor.whiskerRight (comparison H H' F T) G ≫
    Functor.whiskerLeft (Functor.prod F.op F) (comparison H' H'' G U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: The comparison for a composite functor is the composite left-ordered comparison. -/
@[stacks 08I3 "left-ordered pullback internal-Hom comparison composition law"]
theorem comparison_comp
    {E : Type uE} [Category.{vE} E] [MonoidalCategory E]
    (H : MonoidalClosed C) (H' : MonoidalClosed D) (H'' : MonoidalClosed E)
    (F : C ⥤ D) (G : D ⥤ E)
    (T : TensorComparison F) (U : TensorComparison G) :
    comparison H H'' (F ⋙ G) (TensorComparison.comp F G T U) =
      comparisonComp H H' H'' F G T U := by
  ext P
  rcases P with ⟨X, Y⟩
  change comparisonOf H H'' (F ⋙ G) (TensorComparison.comp F G T U) X.unop Y =
    G.map (comparisonOf H H' F T X.unop Y) ≫
      comparisonOf H' H'' G U (F.obj X.unop) (F.obj Y)
  apply ((adjunctionOf H'' ((F ⋙ G).obj X.unop)).homEquiv _ _).symm.injective
  rw [comparisonOf_spec]
  rw [Adjunction.homEquiv_naturality_left_symm]
  have hspecU :
      ((adjunctionOf H'' (G.obj (F.obj X.unop))).homEquiv _ _).symm
          (comparisonOf H' H'' G U (F.obj X.unop) (F.obj Y)) =
        U.inv.app (F.obj X.unop, (ihomOf H' (F.obj X.unop)).obj (F.obj Y)) ≫
          G.map ((adjunctionOf H' (F.obj X.unop)).counit.app (F.obj Y)) := by
    exact comparisonOf_spec H' H'' G U (F.obj X.unop) (F.obj Y)
  change (TensorComparison.comp F G T U).inv.app
      (X.unop, (ihomOf H X.unop).obj Y) ≫
        G.map (F.map ((adjunctionOf H X.unop).counit.app Y)) =
    (tensorLeft (G.obj (F.obj X.unop))).map
        (G.map (comparisonOf H H' F T X.unop Y)) ≫
      ((adjunctionOf H'' (G.obj (F.obj X.unop))).homEquiv _ _).symm
        (comparisonOf H' H'' G U (F.obj X.unop) (F.obj Y))
  rw [hspecU]
  have hU :
      (tensorLeft (G.obj (F.obj X.unop))).map
            (G.map (comparisonOf H H' F T X.unop Y)) ≫
          U.inv.app (F.obj X.unop,
            (ihomOf H' (F.obj X.unop)).obj (F.obj Y)) =
        U.inv.app (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ≫
          G.map ((tensorLeft (F.obj X.unop)).map
            (comparisonOf H H' F T X.unop Y)) := by
    simpa [Functor.tensorFunctor] using
      U.inv.naturality
        (((𝟙 (F.obj X.unop), comparisonOf H H' F T X.unop Y)) :
          (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ⟶
            (F.obj X.unop, (ihomOf H' (F.obj X.unop)).obj (F.obj Y)))
  have hTspec :
      (tensorLeft (F.obj X.unop)).map (comparisonOf H H' F T X.unop Y) ≫
          (adjunctionOf H' (F.obj X.unop)).counit.app (F.obj Y) =
        T.inv.app (X.unop, (ihomOf H X.unop).obj Y) ≫
          F.map ((adjunctionOf H X.unop).counit.app Y) := by
    simpa only [Adjunction.homEquiv_counit] using
      comparisonOf_spec H H' F T X.unop Y
  change (U.inv.app (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ≫
      G.map (T.inv.app (X.unop, (ihomOf H X.unop).obj Y))) ≫
        G.map (F.map ((adjunctionOf H X.unop).counit.app Y)) = _
  calc
    _ = U.inv.app (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ≫
          (G.map (T.inv.app (X.unop, (ihomOf H X.unop).obj Y)) ≫
            G.map (F.map ((adjunctionOf H X.unop).counit.app Y))) :=
      Category.assoc _ _ _
    _ = U.inv.app (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ≫
          G.map (T.inv.app (X.unop, (ihomOf H X.unop).obj Y) ≫
            F.map ((adjunctionOf H X.unop).counit.app Y)) := by
      rw [G.map_comp]
    _ = U.inv.app (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ≫
          G.map ((tensorLeft (F.obj X.unop)).map
            (comparisonOf H H' F T X.unop Y) ≫
              (adjunctionOf H' (F.obj X.unop)).counit.app (F.obj Y)) := by
      rw [hTspec]
    _ = U.inv.app (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ≫
          (G.map ((tensorLeft (F.obj X.unop)).map
              (comparisonOf H H' F T X.unop Y)) ≫
            G.map ((adjunctionOf H' (F.obj X.unop)).counit.app (F.obj Y))) := by
      rw [G.map_comp]
    _ = (U.inv.app (F.obj X.unop, F.obj ((ihomOf H X.unop).obj Y)) ≫
          G.map ((tensorLeft (F.obj X.unop)).map
            (comparisonOf H H' F T X.unop Y))) ≫
          G.map ((adjunctionOf H' (F.obj X.unop)).counit.app (F.obj Y)) :=
      (Category.assoc _ _ _).symm
    _ = ((tensorLeft (G.obj (F.obj X.unop))).map
          (G.map (comparisonOf H H' F T X.unop Y)) ≫
            U.inv.app (F.obj X.unop,
              (ihomOf H' (F.obj X.unop)).obj (F.obj Y))) ≫
          G.map ((adjunctionOf H' (F.obj X.unop)).counit.app (F.obj Y)) := by
      exact congrArg
        (fun k => k ≫ G.map ((adjunctionOf H' (F.obj X.unop)).counit.app (F.obj Y)))
        hU.symm
    _ = _ := Category.assoc _ _ _

/-- 08I3: The identity functor has the identity left-ordered pullback/internal-Hom comparison. -/
@[stacks 08I3 "identity left-ordered pullback internal-Hom comparison"]
theorem comparison_id (H : MonoidalClosed C) :
    comparison H H (𝟭 C) (TensorComparison.id C) =
      𝟙 (sourceFunctor H (𝟭 C)) := by
  ext P
  rcases P with ⟨X, Y⟩
  change comparisonOf H H (𝟭 C) (TensorComparison.id C) X.unop Y = 𝟙 _
  apply ((adjunctionOf H ((𝟭 C).obj X.unop)).homEquiv _ _).symm.injective
  rw [comparisonOf_spec]
  change 𝟙 _ ≫ (adjunctionOf H X.unop).counit.app Y =
    ((adjunctionOf H X.unop).homEquiv _ Y).symm (𝟙 _)
  rw [Category.id_comp, Adjunction.homEquiv_symm_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: Contravariant source naturality of the left-ordered comparison. -/
@[reassoc, stacks 08I3 "left-ordered pullback internal-Hom source naturality"]
theorem comparison_natural_source
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    {X₁ X₂ : C} (f : X₂ ⟶ X₁) (Y : C) :
    F.map ((MonoidalClosed.preOf H f).app Y) ≫ comparisonApp H H' F T X₂ Y =
      comparisonApp H H' F T X₁ Y ≫
        (MonoidalClosed.preOf H' (F.map f)).app (F.obj Y) := by
  have h := comparisonApp_naturality H H' F T
    (P := (Opposite.op X₁, Y)) (Q := (Opposite.op X₂, Y)) (f.op, 𝟙 Y)
  dsimp [sourceFunctor, targetFunctor, Bifunctor.sourceFunctor,
    Bifunctor.targetFunctor, Bifunctor.internalHomFunctor, Functor.uncurry,
    Functor.prod] at h ⊢
  simpa only [Functor.map_id, NatTrans.id_app, preOf_id_app, Category.id_comp,
    Category.comp_id] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: Covariant target naturality of the left-ordered comparison. -/
@[reassoc, stacks 08I3 "left-ordered pullback internal-Hom target naturality"]
theorem comparison_natural_target
    (H : MonoidalClosed C) (H' : MonoidalClosed D)
    (F : C ⥤ D) (T : TensorComparison F)
    (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    F.map ((MonoidalClosed.ihomOf H X).map f) ≫ comparisonApp H H' F T X Y₂ =
      comparisonApp H H' F T X Y₁ ≫
        (MonoidalClosed.ihomOf H' (F.obj X)).map (F.map f) := by
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

end Left

end CategoryTheory.Functor.PullbackInternalHom
