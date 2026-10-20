module

public import Mathlib.CategoryTheory.Sites.Pullback
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
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan

/-- Structure maps of a morphism diagram are continuous for the generated stage topologies. -/
instance toFunctor_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    ((C.map φ).toFunctor).IsContinuous (J m).toGrothendieck (J n).toGrothendieck :=
  (instMorphismDiagram.isExactMorphism φ).toIsContinuous


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
  sorry

/-- Direct-image form of `F(φ)`: restriction along `ofStageNatTrans` yields
`F_m ⟶ (u_φ)_* F_n`. -/
def transitionDirect (A : Type (w + 1)) [Category.{w} A]
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf (topology C J) A) :
    (component C J A m).obj F ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous A
        (J m).toGrothendieck (J n).toGrothendieck).obj
        ((component C J A n).obj F) :=
  (sheafPushforwardContinuousNatTrans (ofStageNatTrans C φ) A
      (J m).toGrothendieck (topology C J)).app F ≫
    (sheafPushforwardContinuousComp (C.map φ).toFunctor (ofStage C n) A
        (J m).toGrothendieck (J n).toGrothendieck (topology C J)).inv.app F

/-- Inverse image `f_φ⁻¹` of sheaves with coefficients in `A` along a simplex operator. -/
def sheafInverseImage (A : Type (w + 1)) [Category.{w} A]
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
  sorry

/-- Inverse image `f_φ⁻¹` of type-valued sheaves along a simplex operator. -/
abbrev inverseImage {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf ((J m).toGrothendieck) (Type w) ⥤ Sheaf ((J n).toGrothendieck) (Type w) :=
  sheafInverseImage C J (Type w) φ

/-- `inverseImage φ` is sheaf pullback along `u_φ`. -/
theorem inverseImage_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    inverseImage C J φ =
      (C.map φ).toFunctor.sheafPullback (Type w) (J m).toGrothendieck (J n).toGrothendieck :=
  sorry

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n` for sheaves with coefficients in `A`, the mate of
`transitionDirect` under continuous sheaf adjunction. -/
def sheafTransition (A : Type (w + 1)) [Category.{w} A]
    [∀ n, HasWeakSheafify (J n).toGrothendieck A]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf (topology C J) A) :
    ((C.map φ).toFunctor.sheafPullback A (J m).toGrothendieck (J n).toGrothendieck).obj
      ((component C J A m).obj F) ⟶ (component C J A n).obj F :=
  (((C.map φ).toFunctor.sheafAdjunctionContinuous A
      (J m).toGrothendieck (J n).toGrothendieck).homEquiv
    ((component C J A m).obj F) ((component C J A n).obj F)).symm
    (transitionDirect C J A φ F)

/-- The adjunction mate of `sheafTransition` is `transitionDirect`. -/
theorem sheafTransition_homEquiv (A : Type (w + 1)) [Category.{w} A]
    [∀ n, HasWeakSheafify (J n).toGrothendieck A]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf (topology C J) A) :
    (((C.map φ).toFunctor.sheafAdjunctionContinuous A
        (J m).toGrothendieck (J n).toGrothendieck).homEquiv
      ((component C J A m).obj F) ((component C J A n).obj F))
      (sheafTransition C J A φ F) =
    transitionDirect C J A φ F :=
  sorry

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n` for type-valued sheaves. -/
abbrev transition {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (topology C J) (Type w)) :
    ((C.map φ).toFunctor.sheafPullback (Type w)
      (J m).toGrothendieck (J n).toGrothendieck).obj
      ((component C J (Type w) m).obj F) ⟶ (component C J (Type w) n).obj F :=
  sheafTransition C J (Type w) φ F

/-- The adjunction mate of `transition` is `transitionDirect`. -/
theorem transition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (topology C J) (Type w)) :
    (((C.map φ).toFunctor.sheafAdjunctionContinuous (Type w)
        (J m).toGrothendieck (J n).toGrothendieck).homEquiv
      ((component C J (Type w) m).obj F) ((component C J (Type w) n).obj F))
      (transition C J φ F) =
    transitionDirect C J (Type w) φ F :=
  sorry

/-- Inverse image `f_φ⁻¹` of abelian sheaves along a simplex operator. -/
abbrev abelianInverseImage {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P] :
    Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} :=
  sheafInverseImage C J AddCommGrpCat.{w} φ

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n` for abelian sheaves. -/
abbrev abelianTransition {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck).obj
      ((component C J AddCommGrpCat.{w} m).obj F) ⟶
    (component C J AddCommGrpCat.{w} n).obj F :=
  sheafTransition C J AddCommGrpCat.{w} φ F

/-- The adjunction mate of `abelianTransition` is `transitionDirect`. -/
theorem abelianTransition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (((C.map φ).toFunctor.sheafAdjunctionContinuous AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck).homEquiv
      ((component C J AddCommGrpCat.{w} m).obj F)
      ((component C J AddCommGrpCat.{w} n).obj F))
      (abelianTransition C J φ F) =
    transitionDirect C J AddCommGrpCat.{w} φ F :=
  sorry

end CategoryTheory.SimplicialSites
