/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian
public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap85.Definition_85_14_1_Ringed
public import stacks_project.Chap85.Lemma_85_3_5_Stage

/-!
# Stage restriction and simplex-operator comparisons on C_total

Restriction `F ↦ F_n` along `ofStage`, the direct-image comparison
`F_m ⟶ (u_φ)_* F_n`, and its mate `F(φ) : f_φ⁻¹ F_m ⟶ F_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsSiteDiagram C J]

/-- Restriction of a sheaf on `C_total` to the degree-`n` site, i.e. `F_n = g_n⁻¹ F`. -/
abbrev component (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory) :
    Sheaf (topology C J) A ⥤ Sheaf ((J n).toGrothendieck) A :=
  stageRestrict C J A n

/-- Sections of `F_n` at `U` are sections of `F` at `(ofStage C n).obj U`. -/
def component_obj (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    (F : Sheaf (topology C J) A) (U : C.obj n) :
    (((component C J A n).obj F).obj.obj (op U)) ≅
      F.obj.obj (op ((ofStage C n).obj U)) :=
  (ofStage C n).sheafPushforwardContinuousObjObjIso A F U

/-- `component C J A n` is continuous sheaf pushforward along `ofStage C n`. -/
theorem component_eq (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory) :
    component C J A n =
      (ofStage C n).sheafPushforwardContinuous A (J n).toGrothendieck (topology C J) :=
  rfl

/-- Inverse image `f_φ⁻¹` of sheaves with coefficients in `A` along a simplex operator. -/
abbrev sheafInverseImage (A : Type (w + 1)) [Category.{w} A]
    [∀ n, HasWeakSheafify (J n).toGrothendieck A]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf ((J m).toGrothendieck) A ⥤ Sheaf ((J n).toGrothendieck) A :=
  (C.map φ).toFunctor.sheafPullback A (J m).toGrothendieck (J n).toGrothendieck

/-- `sheafInverseImage A φ` is sheaf pullback along `u_φ`. -/
theorem sheafInverseImage_eq (A : Type (w + 1)) [Category.{w} A]
    [∀ n, HasWeakSheafify (J n).toGrothendieck A]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    sheafInverseImage C J A φ =
      (C.map φ).toFunctor.sheafPullback A (J m).toGrothendieck (J n).toGrothendieck :=
  rfl

variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Inverse image `f_φ⁻¹` of type-valued sheaves along a simplex operator. -/
abbrev inverseImage {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf ((J m).toGrothendieck) (Type w) ⥤ Sheaf ((J n).toGrothendieck) (Type w) :=
  sheafInverseImage C J (Type w) φ

/-- `inverseImage φ` is sheaf pullback along `u_φ`. -/
theorem inverseImage_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    inverseImage C J φ =
      (C.map φ).toFunctor.sheafPullback (Type w) (J m).toGrothendieck (J n).toGrothendieck :=
  rfl

/-- Inverse image `f_φ⁻¹` of abelian sheaves along a simplex operator. -/
abbrev abelianInverseImage {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P] :
    Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} :=
  sheafInverseImage C J AddCommGrpCat.{w} φ

end CategoryTheory.SimplicialSites
