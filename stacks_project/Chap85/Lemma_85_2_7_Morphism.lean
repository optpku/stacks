/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap85.Lemma_85_2_3
public import stacks_project.Chap85.Lemma_85_2_4_Comparison
public import stacks_project.Chap85.Lemma_85_2_5

/-!
# Zariski morphisms of topoi for simplicial spaces

A morphism `f : Y ⟶ X` of simplicial spaces induces morphisms of topoi
`f_Zar : Sh(Y_Zar) ⟶ Sh(X_Zar)` and `f_n : Sh(Y_n) ⟶ Sh(X_n)`. Inverse images
2-commute with the component morphisms `g_n` of Lemma 85.2.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X)

/-- The morphism of topoi `f_Zar : Sh(Y_Zar) ⟶ Sh(X_Zar)` induced by a morphism of
simplicial spaces. -/
def zariskiMorphism
    [HasWeakSheafify (zariskiTopology Y) (Type u)]
    [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y))] :
    MorphismOfTopoiIn (zariskiTopology X) (zariskiTopology Y) :=
  (zariskiMap f).morphismOfTopoiInOfContinuous (zariskiTopology X) (zariskiTopology Y)

/-- Inverse image of `zariskiMorphism f` is sheaf pullback along `zariskiMap f`. -/
theorem zariskiMorphism_inverseImage
    [HasWeakSheafify (zariskiTopology Y) (Type u)]
    [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y))] :
    (zariskiMorphism f)⁻¹ =
      (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) :=
  sorry

/-- The morphism of topoi `f_n : Sh(Y_n) ⟶ Sh(X_n)` induced by the degree-`n` map of a
morphism of simplicial spaces. -/
def degreeMorphism (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (Opens.map (f.app (op ⦋n⦌))).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((Opens.map (f.app (op ⦋n⦌))).sheafPullback (Type u)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))))] :
    MorphismOfTopoiIn (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
      (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  (Opens.map (f.app (op ⦋n⦌))).morphismOfTopoiInOfContinuous
    (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
    (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))

/-- Inverse image of `degreeMorphism f n` is sheaf pullback along `Opens.map (f.app (op ⦋n⦌))`. -/
theorem degreeMorphism_inverseImage (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (Opens.map (f.app (op ⦋n⦌))).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((Opens.map (f.app (op ⦋n⦌))).sheafPullback (Type u)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))))] :
    (degreeMorphism f n)⁻¹ =
      (Opens.map (f.app (op ⦋n⦌))).sheafPullback (Type u)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  sorry

/-- Inverse images of `f_Zar` and `g_n` 2-commute with inverse images of `g_n` and `f_n`. -/
def zariskiMorphism_comp_component (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [HasWeakSheafify (zariskiTopology Y) (Type u)]
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (Opens.map (f.app (op ⦋n⦌))).op.HasLeftKanExtension P]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F]
    [∀ F : (Opens (Y.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component Y n).op.HasPointwiseRightKanExtension F]
    [PreservesFiniteLimits
      ((zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y))]
    [PreservesFiniteLimits
      ((Opens.map (f.app (op ⦋n⦌))).sheafPullback (Type u)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))))] :
    (zariskiMorphism f)⁻¹ ⋙ (componentMorphism Y n)⁻¹ ≅
      (componentMorphism X n)⁻¹ ⋙ (degreeMorphism f n)⁻¹ :=
  isoWhiskerLeft (LeftExactAdjunction.inverseImage (zariskiMorphism f))
      (componentMorphism_inverseImage_iso_sheafComponent Y n) ≪≫
    zariskiMap_pullbackRestrict f (op ⦋n⦌) ≪≫
    isoWhiskerRight (componentMorphism_inverseImage_iso_sheafComponent X n).symm
      (LeftExactAdjunction.inverseImage (degreeMorphism f n))

/-- The forward map of `zariskiMorphism_comp_component` is the whiskered Beck–Chevalley
comparison of Lemma 85.2.4. -/
theorem zariskiMorphism_comp_component_hom (n : ℕ)
    [HasWeakSheafify (zariskiTopology X) (Type u)]
    [HasWeakSheafify (zariskiTopology Y) (Type u)]
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u)]
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) (Type u)]
    [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
    [∀ P : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (Opens.map (f.app (op ⦋n⦌))).op.HasLeftKanExtension P]
    [∀ F : (Opens (X.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component X n).op.HasPointwiseRightKanExtension F]
    [∀ F : (Opens (Y.obj (op ⦋n⦌)))ᵒᵖ ⥤ Type u,
      (component Y n).op.HasPointwiseRightKanExtension F]
    [PreservesFiniteLimits
      ((zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y))]
    [PreservesFiniteLimits
      ((Opens.map (f.app (op ⦋n⦌))).sheafPullback (Type u)
        (Opens.grothendieckTopology (X.obj (op ⦋n⦌)))
        (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))))] :
    (zariskiMorphism_comp_component f n).hom =
      (isoWhiskerLeft (LeftExactAdjunction.inverseImage (zariskiMorphism f))
          (componentMorphism_inverseImage_iso_sheafComponent Y n) ≪≫
        zariskiMap_pullbackRestrict f (op ⦋n⦌) ≪≫
        isoWhiskerRight (componentMorphism_inverseImage_iso_sheafComponent X n).symm
          (LeftExactAdjunction.inverseImage (degreeMorphism f n))).hom :=
  sorry

end CategoryTheory.SimplicialObject
