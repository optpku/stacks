/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap85.Lemma_85_2_8_Morphism

/-!
# Cartesian sheaves on the Zariski site of a simplicial space

A sheaf on `zariskiTopology Y` is cartesian when every simplex-operator
comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism. An augmentation of
simplicial spaces induces inverse and direct image functors between `Sh(X)`
and `Sh(Y_Zar)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open Functor
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialObject

variable (Y : SimplicialObject TopCat.{u})

/-- The natural transformation `u_φ ⋙ ι_n ⟶ ι_m` whose component at `V` is the
simplex operator `φ`. -/
def componentNatTrans {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Opens.map (Y.map φ.op) ⋙ component Y n ⟶ component Y m where
  app U := DiagramOpens.homMk φ.op fun x hx ↦ hx
  naturality := sorry

/-- The composite of pullback along `Y.map φ.op` with inclusion at degree `n` is continuous. -/
instance component_comp_opensMap_isContinuous {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (Opens.map (Y.map φ.op) ⋙ component Y n).IsContinuous
      (Opens.grothendieckTopology (Y.obj (op ⦋m⦌))) (zariskiTopology Y) :=
  isContinuous_comp (Opens.map (Y.map φ.op)) (component Y n)
    (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (zariskiTopology Y)

/-- Left Kan extensions of coefficient-`A` presheaves along opposite open-map functors
of simplex operators of `Y`. -/
class HasOpensMapLeftKanExtension (A : Type (u + 1)) [Category.{u} A] : Prop where
  /-- Each simplex operator of `Y` admits left Kan extension of `A`-valued presheaves. -/
  out : ∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (P : (Opens (Y.obj (op ⦋m⦌)))ᵒᵖ ⥤ A),
    (Opens.map (Y.map φ.op)).op.HasLeftKanExtension P

/-- Unpack `HasOpensMapLeftKanExtension` at a simplex operator. -/
instance instHasLeftKanExtension_opensMap_of_hasOpensMapLeftKanExtension
    (A : Type (u + 1)) [Category.{u} A] [HasOpensMapLeftKanExtension Y A]
    (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (P : (Opens (Y.obj (op ⦋m⦌)))ᵒᵖ ⥤ A) :
    (Opens.map (Y.map φ.op)).op.HasLeftKanExtension P :=
  HasOpensMapLeftKanExtension.out m n φ P

/-- Open-map left Kan extensions exist for sheaves of sets. -/
instance hasOpensMapLeftKanExtension_type : HasOpensMapLeftKanExtension Y (Type u) where
  out _ _ _ _ := inferInstance

/-- Open-map left Kan extensions exist for abelian sheaves. -/
instance hasOpensMapLeftKanExtension_ab : HasOpensMapLeftKanExtension Y AddCommGrpCat.{u} where
  out _ _ _ _ := inferInstance

section CartesianSheaves

variable (A : Type (u + 1)) [Category.{u} A]
variable [∀ n : ℕ, HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) A]
variable [HasWeakSheafify (zariskiTopology Y) A]
variable [HasOpensMapLeftKanExtension Y A]

/-- Inverse image `f_φ⁻¹` of sheaves with coefficients in `A` along a simplex operator. -/
def sheafInverseImage {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋m⦌))) A ⥤
      Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) A :=
  (Opens.map (Y.map φ.op)).sheafPullback A
    (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))

/-- `sheafInverseImage` is sheaf pullback along `Opens.map (Y.map φ.op)`. -/
theorem sheafInverseImage_eq {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    sheafInverseImage Y A φ =
      (Opens.map (Y.map φ.op)).sheafPullback A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  sorry

/-- Direct-image form of `F(φ)`: restriction along `componentNatTrans` yields
`F_m ⟶ (f_φ)_* F_n`. -/
def transitionDirect {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (G : Sheaf (zariskiTopology Y) A) :
    (sheafComponent Y m A).obj G ⟶
      ((Opens.map (Y.map φ.op)).sheafPushforwardContinuous A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).obj
        ((sheafComponent Y n A).obj G) :=
  (sheafPushforwardContinuousNatTrans (componentNatTrans Y φ) A
      (Opens.grothendieckTopology (Y.obj (op ⦋m⦌))) (zariskiTopology Y)).app G ≫
    (sheafPushforwardContinuousComp (Opens.map (Y.map φ.op)) (component Y n) A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (zariskiTopology Y)).inv.app G

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n`, the mate of `transitionDirect`. -/
def sheafTransition {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (G : Sheaf (zariskiTopology Y) A) :
    (sheafInverseImage Y A φ).obj ((sheafComponent Y m A).obj G) ⟶
      (sheafComponent Y n A).obj G :=
  (((Opens.map (Y.map φ.op)).sheafAdjunctionContinuous A
      (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
      (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).homEquiv
    ((sheafComponent Y m A).obj G) ((sheafComponent Y n A).obj G)).symm
    (transitionDirect Y A φ G)

/-- The adjunction mate of `sheafTransition` is `transitionDirect`. -/
theorem sheafTransition_homEquiv {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (G : Sheaf (zariskiTopology Y) A) :
    (((Opens.map (Y.map φ.op)).sheafAdjunctionContinuous A
        (Opens.grothendieckTopology (Y.obj (op ⦋m⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).homEquiv
      ((sheafComponent Y m A).obj G) ((sheafComponent Y n A).obj G))
      (sheafTransition Y A φ G) =
    transitionDirect Y A φ G :=
  sorry

/-- A sheaf on `Y_Zar` is cartesian when `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian (G : Sheaf (zariskiTopology Y) A) : Prop where
  /-- Every simplex-operator comparison `F(φ)` is an isomorphism. -/
  isIso_transition : ∀ {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌), IsIso (sheafTransition Y A φ G)

/-- Cartesianness is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (G : Sheaf (zariskiTopology Y) A) :
    IsCartesian Y A G ↔
      ∀ {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌), IsIso (sheafTransition Y A φ G) :=
  sorry

/-- A sheaf whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso (G : Sheaf (zariskiTopology Y) A)
    [h : ∀ {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌), IsIso (sheafTransition Y A φ G)] :
    IsCartesian Y A G where
  isIso_transition := h

/-- Every simplex-operator comparison of a cartesian sheaf is an isomorphism. -/
instance instIsIso_sheafTransition (G : Sheaf (zariskiTopology Y) A)
    [IsCartesian Y A G] {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    IsIso (sheafTransition Y A φ G) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` attached to a cartesian sheaf. -/
def transitionIso (G : Sheaf (zariskiTopology Y) A) [IsCartesian Y A G]
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (sheafInverseImage Y A φ).obj ((sheafComponent Y m A).obj G) ≅
      (sheafComponent Y n A).obj G :=
  asIso (sheafTransition Y A φ G)

/-- The forward map of `transitionIso` is `sheafTransition`. -/
theorem transitionIso_hom (G : Sheaf (zariskiTopology Y) A) [IsCartesian Y A G]
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (transitionIso Y A G φ).hom = sheafTransition Y A φ G :=
  sorry

/-- The object property of being a cartesian sheaf on `Y_Zar`. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (zariskiTopology Y) A) :=
  fun G ↦ IsCartesian Y A G

/-- The category of cartesian sheaves on `Y_Zar`. -/
abbrev Cartesian := (cartesianProperty Y A).FullSubcategory

/-- The underlying sheaf of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (G : Cartesian Y A) : IsCartesian Y A G.obj :=
  sorry

end CartesianSheaves

variable {Y}

/-- Inverse image `a⁻¹` along the Zariski augmentation of a simplicial space. -/
def inverseImage {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P] :
    Sheaf (Opens.grothendieckTopology X) B ⥤ Sheaf (zariskiTopology Y) B :=
  (constProjection X).sheafPushforwardContinuous B
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) ⋙
    (zariskiMap a).sheafPullback B (zariskiTopology (constSpace X)) (zariskiTopology Y)

/-- `inverseImage` is the composite of continuous pushforward along `constProjection` with
sheaf pullback along `zariskiMap a`. -/
theorem inverseImage_eq {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P] :
    inverseImage a B =
      (constProjection X).sheafPushforwardContinuous B
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) ⋙
        (zariskiMap a).sheafPullback B (zariskiTopology (constSpace X)) (zariskiTopology Y) :=
  sorry

/-- Direct image `a_*` along the Zariski augmentation of a simplicial space. -/
def directImage {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    Sheaf (zariskiTopology Y) B ⥤ Sheaf (Opens.grothendieckTopology X) B :=
  (zariskiMap a).sheafPushforwardContinuous B
      (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
    (constProjection X).sheafPushforwardCocontinuous B
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)

/-- `directImage` is the composite of continuous pushforward along `zariskiMap a` with
cocontinuous pushforward along `constProjection`. -/
theorem directImage_eq {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    directImage a B =
      (zariskiMap a).sheafPushforwardContinuous B
          (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
        (constProjection X).sheafPushforwardCocontinuous B
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) :=
  sorry

/-- Inverse image is left adjoint to direct image along a Zariski augmentation. -/
def inverseImageAdjunction {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    inverseImage a B ⊣ directImage a B :=
  ((constProjection X).sheafAdjunctionCocontinuous B
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).comp
    ((zariskiMap a).sheafAdjunctionContinuous B
      (zariskiTopology (constSpace X)) (zariskiTopology Y))

/-- Inverse image `a⁻¹ F` of a sheaf on `X` is cartesian on `Y_Zar`. -/
instance inverseImage_isCartesian {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    (B : Type (u + 1)) [Category.{u} B]
    [HasWeakSheafify (zariskiTopology Y) B]
    [HasWeakSheafify (zariskiTopology (constSpace X)) B]
    [HasWeakSheafify (Opens.grothendieckTopology X) B]
    [∀ n : ℕ, HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) B]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ B, (zariskiMap a).op.HasLeftKanExtension P]
    [HasOpensMapLeftKanExtension Y B]
    (F : Sheaf (Opens.grothendieckTopology X) B) :
    IsCartesian Y B ((inverseImage a B).obj F) :=
  sorry

/-- Inverse image of type-valued sheaves along a Zariski augmentation is canonically
isomorphic to `(augmentationMorphism a)⁻¹`. The first factor is `constInverseImageIso`,
comparing continuous pushforward with cocontinuous pullback along `constProjection`. -/
public def inverseImageIso_augmentation {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    inverseImage a (Type u) ≅ (augmentationMorphism a)⁻¹ :=
  isoWhiskerRight (constInverseImageIso).symm
    ((zariskiMap a).sheafPullback (Type u)
      (zariskiTopology (constSpace X)) (zariskiTopology Y))

/-- The forward map of `inverseImageIso_augmentation` is whiskering of
`(constInverseImageIso).inv` by sheaf pullback along `zariskiMap a`. -/
public theorem inverseImageIso_augmentation_hom {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    (inverseImageIso_augmentation a).hom =
      whiskerRight (constInverseImageIso).inv
        ((zariskiMap a).sheafPullback (Type u)
          (zariskiTopology (constSpace X)) (zariskiTopology Y)) :=
  sorry

/-- Essential image of the parallel composite `inverseImage a (Type u)` agrees with that
of the Lemma 85.2.8 inverse image `(augmentationMorphism a)⁻¹`. -/
public theorem mem_essImage_inverseImage_iff_augmentation {X : TopCat.{u}}
    (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    (inverseImage a (Type u)).essImage G ↔ (augmentationMorphism a)⁻¹.essImage G :=
  sorry

/-- Inverse image of a type-valued sheaf along the Lemma 85.2.8 augmentation is cartesian. -/
public instance augmentationMorphism_inverseImage_isCartesian {X : TopCat.{u}}
    (a : Y ⟶ constSpace X)
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ n : ℕ, HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P]
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    IsCartesian Y (Type u) ((augmentationMorphism a)⁻¹.obj F) :=
  sorry

/-- Direct image of type-valued sheaves along a Zariski augmentation is
`(augmentationMorphism a)_*`. -/
theorem directImage_eq_augmentation {X : TopCat.{u}} (a : Y ⟶ constSpace X)
    [HasWeakSheafify (zariskiTopology Y) (Type u)]
    [HasWeakSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
      (constProjection X).op.HasPointwiseRightKanExtension P] :
    directImage a (Type u) = (augmentationMorphism a).pushforward :=
  sorry

end CategoryTheory.SimplicialObject

end

