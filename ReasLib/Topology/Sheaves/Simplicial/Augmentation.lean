/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.ConstantTopos
public import ReasLib.Topology.Sheaves.Simplicial.Functoriality
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.Flat
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Augmentation morphisms of simplicial sheaf topoi

An augmentation induces a geometric morphism whose inverse image is degreewise
topological inverse image and whose direct image is a coface equalizer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section
universe u
namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/-- The continuous map from degree `n` of an augmented simplicial space to its target. -/
def componentSpaceMap (n : ℕ) : Y.obj (op ⦋n⦌) ⟶ X :=
  a.app (op ⦋n⦌)

/-- The degreewise map is the corresponding component of the augmentation. -/
theorem componentSpaceMap_app (n : ℕ) :
    componentSpaceMap a n = a.app (op ⦋n⦌) := rfl

/-- The degreewise augmentation maps commute with every simplicial structure map. -/
theorem component_naturality {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Y.map φ.op ≫ componentSpaceMap a m = componentSpaceMap a n := sorry

/-- The geometric morphism induced by the degreewise continuous augmentation map. -/
def componentTopos (n : ℕ) :
    MorphismOfTopoiIn.{u, u, u, u, u} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  @Functor.morphismOfTopoiInOfContinuous.{u} _ _ _ _
    (Opens.map (componentSpaceMap a n))
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))
    inferInstance inferInstance inferInstance
    (sheafPullbackConstruction.preservesFiniteLimits _ _ _ _)

/-- The inverse image of the degreewise geometric morphism is topological sheaf pullback. -/
theorem componentTopos_inverseImage (n : ℕ) :
    (componentTopos a n)⁻¹ =
      (Opens.map (componentSpaceMap a n)).sheafPullback (Type u)
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) := rfl

/-- An augmentation induces a geometric morphism from simplicial sheaves to target sheaves. -/
def augmentationMorphism :
    MorphismOfTopoiIn.{u, u, u, 0, u} (Opens.grothendieckTopology X) (zariskiTopology Y) :=
  MorphismOfTopoiIn.comp (constMorphism X)
    ((zariskiMap a).morphismOfTopoiInOfContinuous.{u}
      (zariskiTopology (constSpace X)) (zariskiTopology Y))

/-- Augmentation inverse image is constant-space inverse image followed by site pullback. -/
theorem augmentationMorphism_inverseImage :
    (augmentationMorphism a)⁻¹ = (constMorphism X)⁻¹ ⋙
      (zariskiMap a).sheafPullback (Type u)
        (zariskiTopology (constSpace X)) (zariskiTopology Y) := rfl

/-- Restriction of augmentation inverse image is inverse image along the degreewise map. -/
def inverseImage_component (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (sheafComponent Y n (Type u)).obj ((augmentationMorphism a)⁻¹.obj F) ≅
      (componentTopos a n)⁻¹.obj F :=
  (sheafComponent Y n (Type u)).mapIso
      (((zariskiMap a).sheafPullback (Type u)
        (zariskiTopology (constSpace X)) (zariskiTopology Y)).mapIso
          ((constMorphism_inverseImage_iso X).app F)) ≪≫
    (zariskiMap_pullbackRestrict a (op ⦋n⦌)).app
      (((constProjection X).sheafPushforwardContinuous (Type u)
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).obj F) ≪≫
    (componentTopos a n)⁻¹.mapIso (inverseImage_const_app X ⦋n⦌ F)

/-- The degreewise inverse-image comparisons are natural in the target sheaf. -/
def inverseImage_sheafComponent (n : ℕ) :
    (augmentationMorphism a)⁻¹ ⋙ sheafComponent Y n (Type u) ≅ (componentTopos a n)⁻¹ :=
  NatIso.ofComponents (fun F ↦ inverseImage_component a n F) sorry

/-- Evaluation of the natural inverse-image comparison is the degreewise comparison. -/
theorem inverseImage_sheafComponent_app (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (inverseImage_sheafComponent a n).app F = inverseImage_component a n F := rfl

/-- Composing augmentation and component geometric morphisms recovers the degreewise map. -/
def comp_component (n : ℕ) :
    (augmentationMorphism a)⁻¹ ⋙ (componentMorphism Y n)⁻¹ ≅ (componentTopos a n)⁻¹ :=
  isoWhiskerLeft ((augmentationMorphism a)⁻¹)
    (componentMorphism_inverseImage_iso_sheafComponent Y n) ≪≫
      inverseImage_sheafComponent a n

namespace Augmentation

/-- Direct image to the constant simplicial space of the augmentation target. -/
private abbrev zariskiPushforward (G : Sheaf (zariskiTopology Y) (Type u)) :
    Sheaf (zariskiTopology (constSpace X)) (Type u) :=
  ((zariskiMap a).sheafPushforwardContinuous (Type u)
    (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G

/-- The canonical comparison from augmentation direct image to degree-zero direct image. -/
def pushforwardι (G : Sheaf (zariskiTopology Y) (Type u)) :
    (augmentationMorphism a).pushforward.obj G ⟶
      (componentTopos a 0).pushforward.obj ((sheafComponent Y 0 (Type u)).obj G) := by
  exact SimplicialObject.pushforwardι X (((zariskiMap a).sheafPushforwardContinuous (Type u)
      (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G) ≫
    (zariskiPushforward_component a (op ⦋0⦌) G).hom

/-- The two degree-zero coface maps on componentwise direct images. -/
def pushforwardParallel (G : Sheaf (zariskiTopology Y) (Type u)) (i : Fin 2) :
    (componentTopos a 0).pushforward.obj ((sheafComponent Y 0 (Type u)).obj G) ⟶
      (componentTopos a 1).pushforward.obj ((sheafComponent Y 1 (Type u)).obj G) := by
  exact (zariskiPushforward_component a (op ⦋0⦌) G).inv ≫
    ((toCosimplicial X (Type u)).obj (((zariskiMap a).sheafPushforwardContinuous (Type u)
      (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G)).δ i ≫
      (zariskiPushforward_component a (op ⦋1⦌) G).hom

/-- The component pushforward comparisons transport each coface map to its degreewise map. -/
theorem pushforwardParallel_comm (G : Sheaf (zariskiTopology Y) (Type u)) (i : Fin 2) :
    (zariskiPushforward_component a (op ⦋0⦌) G).hom ≫ pushforwardParallel a G i =
      ((toCosimplicial X (Type u)).obj
        (((zariskiMap a).sheafPushforwardContinuous (Type u)
          (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G)).δ i ≫
        (zariskiPushforward_component a (op ⦋1⦌) G).hom := sorry

/-- The comparison to degree zero equalizes the two coface-induced direct-image maps. -/
theorem pushforwardFork_condition (G : Sheaf (zariskiTopology Y) (Type u)) :
    pushforwardι a G ≫ pushforwardParallel a G 0 =
      pushforwardι a G ≫ pushforwardParallel a G 1 := sorry

/-- The fork with augmentation direct image as apex and the two cofaces as parallel arrows. -/
def pushforwardFork (G : Sheaf (zariskiTopology Y) (Type u)) :
    Fork (pushforwardParallel a G 0) (pushforwardParallel a G 1) :=
  Fork.ofι (pushforwardι a G) (pushforwardFork_condition a G)

/-- Augmentation direct image is the equalizer of the two degree-zero coface maps. -/
def pushforwardFork_isLimit (G : Sheaf (zariskiTopology Y) (Type u)) :
    IsLimit (pushforwardFork a G) := by
  exact Fork.isLimitOfIsos
    (SimplicialObject.pushforwardFork X (((zariskiMap a).sheafPushforwardContinuous (Type u)
      (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G))
    (SimplicialObject.pushforwardFork_isLimit X (((zariskiMap a).sheafPushforwardContinuous (Type u)
      (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj G))
    (pushforwardFork a G)
    (zariskiPushforward_component a (op ⦋0⦌) G)
    (zariskiPushforward_component a (op ⦋1⦌) G)
    (Iso.refl _)
    (pushforwardParallel_comm a G 0)
    (pushforwardParallel_comm a G 1)
    (by change 𝟙 _ ≫ pushforwardι a G = _; rw [Category.id_comp]; rfl)

end Augmentation
end CategoryTheory.SimplicialObject
