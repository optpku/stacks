/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap85.Lemma_85_33_1_Etale

/-!
# Cartesian sheaves on the spaces-étale total site

A sheaf on `spacesEtaleTotalTopology U` is cartesian when every simplex-operator
comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Identity-degree inclusion of the degree-`n` spaces-étale site is continuous for the
total spaces-étale topology. -/
instance includeStage_isContinuous (n : SimplexCategoryᵒᵖ) :
    (SpacesEtale.includeStage n).IsContinuous
      (spacesEtaleTopology (U.obj n)) (spacesEtaleTotalTopology U) :=
  sorry

/-- The composite of pullback along `U.map φ.op` with inclusion at degree `n` is continuous. -/
instance includeStage_comp_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (spacesEtalePullback (U.map φ.op) ⋙ SpacesEtale.includeStage (op n)).IsContinuous
      (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTotalTopology U) :=
  isContinuous_comp (spacesEtalePullback (U.map φ.op)) (SpacesEtale.includeStage (op n))
    (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTopology (U.obj (op n)))
    (spacesEtaleTotalTopology U)

/-- Opposite of `spacesEtalePullback f` admits left Kan extensions of coefficient-`A`
presheaves. -/
instance spacesEtalePullback_op_hasLeftKanExtension {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : Type (u + 2)) [Category.{u + 1} A] (P : (spacesEtaleSite Y)ᵒᵖ ⥤ A) :
    (spacesEtalePullback f).op.HasLeftKanExtension P :=
  sorry

/-- The natural transformation `u_φ ⋙ ι_n ⟶ ι_m` whose component at `V` is the commutative
square with simplex operator `φ`. -/
def includeStageNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    spacesEtalePullback (U.map φ.op) ⋙ SpacesEtale.includeStage (op n) ⟶
      SpacesEtale.includeStage (op m) where
  app V := SpacesEtale.homEquivFromPullback φ (𝟙 _)
  naturality := sorry

variable (A : Type (u + 2)) [Category.{u + 1} A]
variable [∀ n : SimplexCategoryᵒᵖ, HasWeakSheafify (spacesEtaleTopology (U.obj n)) A]
variable [HasWeakSheafify (spacesEtaleTotalTopology U) A]

/-- Restriction of a sheaf on `U_étale` to the degree-`n` spaces-étale site. -/
def component (n : SimplexCategory) :
    Sheaf (spacesEtaleTotalTopology U) A ⥤ Sheaf (spacesEtaleTopology (U.obj (op n))) A :=
  (SpacesEtale.includeStage (op n)).sheafPushforwardContinuous A
    (spacesEtaleTopology (U.obj (op n))) (spacesEtaleTotalTopology U)

/-- `component U A n` is continuous sheaf pushforward along `includeStage (op n)`. -/
theorem component_eq (n : SimplexCategory) :
    component U A n =
      (SpacesEtale.includeStage (op n)).sheafPushforwardContinuous A
        (spacesEtaleTopology (U.obj (op n))) (spacesEtaleTotalTopology U) :=
  sorry

/-- Inverse image `f_φ⁻¹` of sheaves with coefficients in `A` along a simplex operator. -/
def sheafInverseImage {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf (spacesEtaleTopology (U.obj (op m))) A ⥤
      Sheaf (spacesEtaleTopology (U.obj (op n))) A :=
  (spacesEtalePullback (U.map φ.op)).sheafPullback A
    (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTopology (U.obj (op n)))

/-- `sheafInverseImage` is sheaf pullback along `spacesEtalePullback (U.map φ.op)`. -/
theorem sheafInverseImage_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    sheafInverseImage U A φ =
      (spacesEtalePullback (U.map φ.op)).sheafPullback A
        (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTopology (U.obj (op n))) :=
  sorry

/-- Direct-image form of `F(φ)`: restriction along `includeStageNatTrans` yields
`F_m ⟶ (f_φ)_* F_n`. -/
def transitionDirect {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (spacesEtaleTotalTopology U) A) :
    (component U A m).obj G ⟶
      ((spacesEtalePullback (U.map φ.op)).sheafPushforwardContinuous A
        (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTopology (U.obj (op n)))).obj
        ((component U A n).obj G) :=
  (sheafPushforwardContinuousNatTrans (includeStageNatTrans U φ) A
      (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTotalTopology U)).app G ≫
    (sheafPushforwardContinuousComp (spacesEtalePullback (U.map φ.op))
        (SpacesEtale.includeStage (op n)) A
        (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTopology (U.obj (op n)))
        (spacesEtaleTotalTopology U)).inv.app G

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n`, the mate of `transitionDirect`. -/
def sheafTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (spacesEtaleTotalTopology U) A) :
    (sheafInverseImage U A φ).obj ((component U A m).obj G) ⟶ (component U A n).obj G :=
  (((spacesEtalePullback (U.map φ.op)).sheafAdjunctionContinuous A
      (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTopology (U.obj (op n)))).homEquiv
    ((component U A m).obj G) ((component U A n).obj G)).symm
    (transitionDirect U A φ G)

/-- The adjunction mate of `sheafTransition` is `transitionDirect`. -/
theorem sheafTransition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (spacesEtaleTotalTopology U) A) :
    (((spacesEtalePullback (U.map φ.op)).sheafAdjunctionContinuous A
        (spacesEtaleTopology (U.obj (op m))) (spacesEtaleTopology (U.obj (op n)))).homEquiv
      ((component U A m).obj G) ((component U A n).obj G))
      (sheafTransition U A φ G) =
    transitionDirect U A φ G :=
  sorry

/-- A sheaf on `U_étale` is cartesian when `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian (G : Sheaf (spacesEtaleTotalTopology U) A) : Prop where
  /-- Every simplex-operator comparison `F(φ)` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (sheafTransition U A φ G)

/-- Cartesianness is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (G : Sheaf (spacesEtaleTotalTopology U) A) :
    IsCartesian U A G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (sheafTransition U A φ G) :=
  sorry

/-- A sheaf whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso (G : Sheaf (spacesEtaleTotalTopology U) A)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (sheafTransition U A φ G)] :
    IsCartesian U A G where
  isIso_transition := h

/-- Every simplex-operator comparison of a cartesian sheaf is an isomorphism. -/
instance instIsIso_sheafTransition (G : Sheaf (spacesEtaleTotalTopology U) A)
    [IsCartesian U A G] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (sheafTransition U A φ G) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` attached to a cartesian sheaf. -/
def transitionIso (G : Sheaf (spacesEtaleTotalTopology U) A) [IsCartesian U A G]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (sheafInverseImage U A φ).obj ((component U A m).obj G) ≅ (component U A n).obj G :=
  asIso (sheafTransition U A φ G)

/-- The forward map of `transitionIso` is `sheafTransition`. -/
theorem transitionIso_hom (G : Sheaf (spacesEtaleTotalTopology U) A) [IsCartesian U A G]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso U A G φ).hom = sheafTransition U A φ G :=
  sorry

/-- The object property of being a cartesian sheaf on `U_étale`. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (spacesEtaleTotalTopology U) A) :=
  fun G ↦ IsCartesian U A G

/-- The category of cartesian sheaves on `U_étale`. -/
abbrev Cartesian := (cartesianProperty U A).FullSubcategory

/-- The underlying sheaf of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (G : Cartesian U A) : IsCartesian U A G.obj :=
  sorry

variable {X : AlgebraicSpace S} (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
variable [∀ P : (spacesEtaleSite X)ᵒᵖ ⥤ A, (augmentationFunctor U a).op.HasLeftKanExtension P]

/-- Inverse image `a⁻¹` along the spaces-étale augmentation. -/
def inverseImage : Sheaf (spacesEtaleTopology X) A ⥤ Sheaf (spacesEtaleTotalTopology U) A :=
  (augmentationFunctor U a).sheafPullback A (spacesEtaleTopology X) (spacesEtaleTotalTopology U)

/-- `inverseImage` is sheaf pullback along `augmentationFunctor a`. -/
theorem inverseImage_eq :
    inverseImage U A a =
      (augmentationFunctor U a).sheafPullback A
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U) :=
  sorry

/-- Direct image `a_*` along the spaces-étale augmentation. -/
def directImage : Sheaf (spacesEtaleTotalTopology U) A ⥤ Sheaf (spacesEtaleTopology X) A :=
  (augmentationFunctor U a).sheafPushforwardContinuous A
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U)

/-- `directImage` is continuous sheaf pushforward along `augmentationFunctor a`. -/
theorem directImage_eq :
    directImage U A a =
      (augmentationFunctor U a).sheafPushforwardContinuous A
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U) :=
  sorry

/-- Inverse image `a⁻¹ F` of a sheaf on `X_étale` is cartesian on `U_étale`. -/
instance inverseImage_isCartesian (F : Sheaf (spacesEtaleTopology X) A) :
    IsCartesian U A ((inverseImage U A a).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
