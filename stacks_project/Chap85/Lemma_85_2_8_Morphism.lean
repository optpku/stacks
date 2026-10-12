/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap85.Lemma_85_2_12_Projection
public import stacks_project.Chap85.Lemma_85_2_3
public import stacks_project.Chap85.Lemma_85_2_5

/-!
# Augmentation morphism of topoi

An augmentation `a : Y ⟶ constSpace X` of a simplicial space induces a morphism of topoi
`Sh(Y_Zar) ⟶ Sh(X)` by composing the site morphism of `zariskiMap a` with the degree-forgetting
projection of the constant simplicial space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/-- The degree-`n` continuous map `a_n : Y_n ⟶ X` of an augmentation. -/
def componentSpaceMap (n : ℕ) : Y.obj (op ⦋n⦌) ⟶ X :=
  a.app (op ⦋n⦌)

/-- `componentSpaceMap a n` is the degree-`n` component of the augmentation. -/
theorem componentSpaceMap_app (n : ℕ) :
    componentSpaceMap a n = a.app (op ⦋n⦌) :=
  sorry

/-- Space-level naturality `a_m ∘ Y(φ) = a_n` of an augmentation. -/
theorem component_naturality {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Y.map φ.op ≫ componentSpaceMap a m = componentSpaceMap a n :=
  sorry

/-- The identity-on-objects isomorphism
`component (constSpace X) n ⋙ zariskiMap a ≅
Opens.map (componentSpaceMap a n) ⋙ component Y n`. -/
def zariskiMap_component (n : ℕ) :
    component (constSpace X) n ⋙ zariskiMap a ≅
      Opens.map (componentSpaceMap a n) ⋙ component Y n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- Components of `zariskiMap_component` are identity morphisms. -/
theorem zariskiMap_component_hom_app (n : ℕ) (U : Opens X) :
    (zariskiMap_component a n).hom.app U = 𝟙 _ :=
  sorry

/-- Continuity of `Opens.map (componentSpaceMap a n)` between the degree-`n` constant space
and `Y_n`. -/
instance componentSpaceMap_isContinuous (n : ℕ) :
    (Opens.map (componentSpaceMap a n)).IsContinuous
      (Opens.grothendieckTopology ((constSpace X).obj (op ⦋n⦌)))
      (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  sorry

/-- Continuity of `Opens.map (componentSpaceMap a n) ⋙ component Y n`, transported from
`component (constSpace X) n ⋙ zariskiMap a`. -/
instance zariskiMap_component_isContinuous (n : ℕ) :
    (Opens.map (componentSpaceMap a n) ⋙ component Y n).IsContinuous
      (Opens.grothendieckTopology ((constSpace X).obj (op ⦋n⦌))) (zariskiTopology Y) :=
  sorry

/-- Inverse image of type-valued sheaves along `zariskiMap a` preserves finite limits. -/
instance zariskiMap_sheafPullback_preservesFiniteLimits
    [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
    [HasSheafify (zariskiTopology Y) (Type u)]
    [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u, (zariskiMap a).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((zariskiMap a).sheafPullback (Type u) (zariskiTopology (constSpace X))
        (zariskiTopology Y)) :=
  sorry

/-- Inverse image of type-valued sheaves along `Opens.map (componentSpaceMap a n)` preserves
finite limits. -/
instance componentSpaceMap_sheafPullback_preservesFiniteLimits (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology X) (Type u)]
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((Opens.map (componentSpaceMap a n)).sheafPullback (Type u)
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))) :=
  sorry

variable [HasSheafify (zariskiTopology (constSpace X)) (Type u)]
variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
    (constProjection X).op.HasPointwiseRightKanExtension F]
variable [∀ P : (zariskiSite (constSpace X))ᵒᵖ ⥤ Type u,
    (zariskiMap a).op.HasLeftKanExtension P]

/-- The morphism of topoi `a_n : Sh(Y_n) ⟶ Sh(X)` associated to the degree-`n` map of an
augmentation. -/
def componentTopos (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    MorphismOfTopoiIn (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  (Opens.map (componentSpaceMap a n)).morphismOfTopoiInOfContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))

/-- Inverse image of `componentTopos a n` is sheaf pullback along `Opens.map (componentSpaceMap a n)`. -/
theorem componentTopos_inverseImage (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    (componentTopos a n)⁻¹ =
      (Opens.map (componentSpaceMap a n)).sheafPullback (Type u)
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  sorry

/-- The canonical morphism of topoi `a : Sh(Y_Zar) ⟶ Sh(X)` induced by an augmentation. -/
def augmentationMorphism :
    MorphismOfTopoiIn (Opens.grothendieckTopology X) (zariskiTopology Y) :=
  MorphismOfTopoiIn.comp
    ((constProjection X).morphismOfTopoiInOfCocontinuous
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X))
    ((zariskiMap a).morphismOfTopoiInOfContinuous
      (zariskiTopology (constSpace X)) (zariskiTopology Y))

/-- Inverse image of `augmentationMorphism a` is the composite of the inverse images of
`zariskiMap a` and of the constant-space projection. -/
theorem augmentationMorphism_inverseImage :
    (augmentationMorphism a)⁻¹ =
      ((constProjection X).morphismOfTopoiInOfCocontinuous
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X))⁻¹ ⋙
        ((zariskiMap a).morphismOfTopoiInOfContinuous
          (zariskiTopology (constSpace X)) (zariskiTopology Y))⁻¹ :=
  sorry

/-- Cocontinuous inverse image along `constProjection` agrees with continuous pushforward. -/
def constInverseImageIso :
    ((constProjection X).morphismOfTopoiInOfCocontinuous
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X))⁻¹ ≅
      (constProjection X).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) where
  hom := CocontinuousPullback.comparison (constProjection X)
    (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)
  inv := NatTrans.mk
    (fun F ↦
      ((constProjection X).sheafPushforwardContinuous (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).map
        (sheafificationIso F).hom ≫
        ((constProjection X).pushforwardContinuousSheafificationCompatibility (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).inv.app F.obj)
    sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `constInverseImageIso` is the cocontinuous-to-continuous comparison. -/
theorem constInverseImageIso_hom :
    constInverseImageIso.hom =
      CocontinuousPullback.comparison (constProjection X)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) :=
  sorry

/-- Cocontinuous inverse image along the degree-`n` inclusion agrees with restriction. -/
def componentInverseImageIso (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ F : (Opens (Y.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component Y n).op.HasPointwiseRightKanExtension F] :
    (componentMorphism Y n)⁻¹ ≅ sheafComponent Y n (Type u) where
  hom := CocontinuousPullback.comparison (component Y n)
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (zariskiTopology Y)
  inv := NatTrans.mk
    (fun F ↦
      (sheafComponent Y n (Type u)).map (sheafificationIso F).hom ≫
        ((component Y n).pushforwardContinuousSheafificationCompatibility (Type u)
          (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (zariskiTopology Y)).inv.app F.obj)
    sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `componentInverseImageIso` is the cocontinuous-to-continuous comparison. -/
theorem componentInverseImageIso_hom (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ F : (Opens (Y.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component Y n).op.HasPointwiseRightKanExtension F] :
    (componentInverseImageIso n).hom =
      CocontinuousPullback.comparison (component Y n)
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (zariskiTopology Y) :=
  sorry

/-- Degree-`n` restriction of continuous inverse image along `constProjection` is the
identity on sheaves on `X`. -/
def constRestrictDegree (n : SimplexCategory)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    ((toCosimplicial X (Type u)).obj
        (((constProjection X).sheafPushforwardContinuous (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).obj F)).obj n ≅ F :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) (Type u)).preimageIso
    (isoWhiskerRight ((NatIso.op (fiber_comp_constProjection X (op n))).symm) F.obj ≪≫
      F.obj.leftUnitor)

/-- On the underlying presheaf, `constRestrictDegree` is whiskering by the inverse of
`fiber_comp_constProjection`. -/
theorem constRestrictDegree_presheaf (n : SimplexCategory)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    ((constRestrictDegree n F).hom).hom =
      (isoWhiskerRight ((NatIso.op (fiber_comp_constProjection X (op n))).symm) F.obj ≪≫
        F.obj.leftUnitor).hom :=
  sorry

/-- Restriction of `constProjection` inverse image to degree `n` recovers the original sheaf. -/
def constDegreeRestrictIso (n : ℕ) :
    (constProjection X).sheafPushforwardContinuous (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) ⋙
        sheafComponent (constSpace X) n (Type u) ≅
      𝟭 (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  NatIso.ofComponents (fun F ↦ constRestrictDegree ⦋n⦌ F) sorry

/-- `constDegreeRestrictIso` evaluates as `constRestrictDegree`. -/
theorem constDegreeRestrictIso_app (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (constDegreeRestrictIso n).app F = constRestrictDegree ⦋n⦌ F :=
  sorry

/-- Pushforward along `zariskiMap a` then restrict to degree `n` is isomorphic to restrict
to `Y_n` then pushforward along `a_n`. -/
def zariskiPushforward_restrict (n : ℕ) :
    (zariskiMap a).sheafPushforwardContinuous (Type u)
          (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
        sheafComponent (constSpace X) n (Type u) ≅
      sheafComponent Y n (Type u) ⋙ (componentTopos a n).pushforward :=
  Iso.refl _

/-- The forward map of `zariskiPushforward_restrict` is the identification of continuous
pushforwards along `zariskiMap_component`. -/
theorem zariskiPushforward_restrict_hom (n : ℕ) :
    (zariskiPushforward_restrict a n).hom = 𝟙 _ :=
  sorry

/-- The mixed Beck–Chevalley mate of `zariskiPushforward_restrict`. -/
def zariskiPullback_restrict_mate (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    sheafComponent (constSpace X) n (Type u) ⋙ (componentTopos a n)⁻¹ ⟶
      (zariskiMap a).sheafPullback (Type u)
          (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
        sheafComponent Y n (Type u) :=
  (mateEquiv
      ((zariskiMap a).sheafAdjunctionContinuous (Type u)
        (zariskiTopology (constSpace X)) (zariskiTopology Y))
      ((Opens.map (componentSpaceMap a n)).sheafAdjunctionContinuous (Type u)
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))))).symm
    (TwoSquare.mk _ _ _ _ (zariskiPushforward_restrict a n).hom)

/-- The mixed Beck–Chevalley mate is invertible, as the corresponding pushforward
comparison is an isomorphism. -/
instance zariskiPullback_restrict_mate_isIso (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    IsIso (zariskiPullback_restrict_mate a n) :=
  sorry

/-- The mixed Beck–Chevalley isomorphism
`(a_Zar⁻¹ ⋙ restrict_Y) ≅ (restrict_X ⋙ a_n⁻¹)` of `zariskiPushforward_restrict`.
The right-to-left morphism is `zariskiPullback_restrict_mate`. -/
def zariskiPullback_restrict (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    (zariskiMap a).sheafPullback (Type u)
          (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
        sheafComponent Y n (Type u) ≅
      sheafComponent (constSpace X) n (Type u) ⋙ (componentTopos a n)⁻¹ :=
  (asIso (zariskiPullback_restrict_mate a n)).symm

/-- `a⁻¹ F` restricts on `Y_n` to `a_n⁻¹ F`. -/
def inverseImage_component (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P]
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (sheafComponent Y n (Type u)).obj ((augmentationMorphism a)⁻¹.obj F) ≅
      (componentTopos a n)⁻¹.obj F :=
  let H :=
    ((constProjection X).sheafPushforwardContinuous (Type u)
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).obj F
  ((sheafComponent Y n (Type u)).mapIso
      (((zariskiMap a).sheafPullback (Type u)
          (zariskiTopology (constSpace X)) (zariskiTopology Y)).mapIso
        (constInverseImageIso.app F))) ≪≫
    (zariskiPullback_restrict a n).app H ≪≫
      ((componentTopos a n)⁻¹.mapIso ((constDegreeRestrictIso n).app F))

/-- Underlying morphism of `inverseImage_component`. -/
theorem inverseImage_component_hom (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P]
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (inverseImage_component a n F).hom =
      (((sheafComponent Y n (Type u)).mapIso
          (((zariskiMap a).sheafPullback (Type u)
              (zariskiTopology (constSpace X)) (zariskiTopology Y)).mapIso
            (constInverseImageIso.app F))) ≪≫
        (zariskiPullback_restrict a n).app
          (((constProjection X).sheafPushforwardContinuous (Type u)
              (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).obj F) ≪≫
          ((componentTopos a n)⁻¹.mapIso ((constDegreeRestrictIso n).app F))).hom :=
  sorry

/-- Restriction after `a⁻¹` is inverse image along `a_n`. -/
def inverseImage_sheafComponent (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    (augmentationMorphism a)⁻¹ ⋙ sheafComponent Y n (Type u) ≅ (componentTopos a n)⁻¹ :=
  NatIso.ofComponents (fun F ↦ inverseImage_component a n F) sorry

/-- `inverseImage_sheafComponent` evaluates as `inverseImage_component`. -/
theorem inverseImage_sheafComponent_app (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P]
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (inverseImage_sheafComponent a n).app F = inverseImage_component a n F :=
  sorry

/-- Inverse image of `a ∘ g_n` is inverse image of the degree-`n` space map `a_n`. -/
def comp_component (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ F : (Opens (Y.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component Y n).op.HasPointwiseRightKanExtension F]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    (augmentationMorphism a)⁻¹ ⋙ (componentMorphism Y n)⁻¹ ≅ (componentTopos a n)⁻¹ :=
  isoWhiskerLeft (LeftExactAdjunction.inverseImage (augmentationMorphism a))
      (componentInverseImageIso n) ≪≫
    inverseImage_sheafComponent a n

/-- The forward functor of `comp_component` is `g_n⁻¹` after `a⁻¹`. -/
theorem comp_component_hom (n : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ F : (Opens (Y.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component Y n).op.HasPointwiseRightKanExtension F]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P] :
    (comp_component a n).hom =
      (isoWhiskerLeft (LeftExactAdjunction.inverseImage (augmentationMorphism a))
          (componentInverseImageIso n) ≪≫
        inverseImage_sheafComponent a n).hom :=
  sorry

/-- Direct image of `zariskiMap a` applied to a sheaf on `Y_Zar`. -/
def zariskiPushforward (G : Sheaf (zariskiTopology Y) (Type u)) :
    Sheaf (zariskiTopology (constSpace X)) (Type u) :=
  ((zariskiMap a).sheafPushforwardContinuous (Type u)
    (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G

/-- `zariskiPushforward a G` is continuous sheaf pushforward along `zariskiMap a`. -/
theorem zariskiPushforward_obj (G : Sheaf (zariskiTopology Y) (Type u)) :
    zariskiPushforward a G =
      ((zariskiMap a).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G :=
  sorry

/-- Degree `n` of `(zariskiMap a)_* G` is `a_{n,*} G_n`. -/
def zariskiPushforward_componentIso (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    ((toCosimplicial X (Type u)).obj (zariskiPushforward a G)).obj ⦋n⦌ ≅
      (componentTopos a n).pushforward.obj ((sheafComponent Y n (Type u)).obj G) :=
  (zariskiPushforward_restrict a n).app G

/-- `zariskiPushforward_componentIso` is the mixed pushforward comparison in degree `n`. -/
theorem zariskiPushforward_componentIso_hom (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a n)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    (zariskiPushforward_componentIso a n G).hom =
      (zariskiPushforward_restrict a n).hom.app G :=
  sorry

/-- The comparison from `a_* G` to `a_{0,*} G_0`. -/
def pushforwardι
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋0⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 0)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    (augmentationMorphism a).pushforward.obj G ⟶
      (componentTopos a 0).pushforward.obj ((sheafComponent Y 0 (Type u)).obj G) :=
  (constRestrictDegree ⦋0⦌ ((augmentationMorphism a).pushforward.obj G)).inv ≫
    ((toCosimplicial X (Type u)).map
      (((constProjection X).sheafAdjunctionCocontinuous (Type u)
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).counit.app
        (zariskiPushforward a G))).app ⦋0⦌ ≫
    (zariskiPushforward_componentIso a 0 G).hom

/-- The two maps `a_{0,*} G_0 ⇉ a_{1,*} G_1` induced by `SimplexCategory.δ`. -/
def pushforwardParallel
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋0⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋1⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 0)).op.HasLeftKanExtension P]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 1)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) (i : Fin 2) :
    (componentTopos a 0).pushforward.obj ((sheafComponent Y 0 (Type u)).obj G) ⟶
      (componentTopos a 1).pushforward.obj ((sheafComponent Y 1 (Type u)).obj G) :=
  (zariskiPushforward_componentIso a 0 G).inv ≫
    ((toCosimplicial X (Type u)).obj (zariskiPushforward a G)).δ i ≫
    (zariskiPushforward_componentIso a 1 G).hom

/-- The two coface maps coequalize `pushforwardι`. -/
theorem pushforwardFork_condition
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋0⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋1⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 0)).op.HasLeftKanExtension P]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 1)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    pushforwardι a G ≫ pushforwardParallel a G 0 =
      pushforwardι a G ≫ pushforwardParallel a G 1 :=
  sorry

/-- The fork presenting `a_* G` as a candidate equalizer of `a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
def pushforwardFork
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋0⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋1⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 0)).op.HasLeftKanExtension P]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 1)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    Fork (pushforwardParallel a G 0) (pushforwardParallel a G 1) :=
  Fork.ofι (pushforwardι a G) (pushforwardFork_condition a G)

/-- The mediating morphism from a test cone into `a_* G`, obtained by adjunction from the
degree-zero comparison of the test cone. -/
def pushforwardForkLift
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋0⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋1⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 0)).op.HasLeftKanExtension P]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 1)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u))
    (s : Fork (pushforwardParallel a G 0) (pushforwardParallel a G 1)) :
    s.pt ⟶ (augmentationMorphism a).pushforward.obj G :=
  ((constProjection X).sheafAdjunctionCocontinuous (Type u)
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).homEquiv
    s.pt (zariskiPushforward a G)
    (ObjectProperty.homMk
      { app := fun U ↦
          let V := U.unop
          (Fork.ι s ≫ (zariskiPushforward_componentIso a 0 G).inv).hom.app (op V.opens) ≫
            (zariskiPushforward a G).obj.map
              (Quiver.Hom.op
                (DiagramOpens.homMk
                  (SimplexCategory.const ⦋0⦌ V.base.unop 0).op fun x hx ↦ hx))
        naturality := sorry })

/-- `a_* G` is the equalizer of the two maps `a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
def pushforwardFork_isLimit
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋0⦌))) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋1⦌))) (Type u)]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 0)).op.HasLeftKanExtension P]
    [∀ P : (Opens X)ᵒᵖ ⥤ Type u,
      (Opens.map (componentSpaceMap a 1)).op.HasLeftKanExtension P]
    (G : Sheaf (zariskiTopology Y) (Type u)) :
    IsLimit (pushforwardFork a G) :=
  Fork.IsLimit.mk (pushforwardFork a G) (pushforwardForkLift a G) sorry sorry

end CategoryTheory.SimplicialObject
