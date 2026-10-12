/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_2_4_RightSquare
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Functors
public import stacks_project.Chap85.Lemma_85_2_1_Opens
public import stacks_project.Chap85.Lemma_85_2_1_Site
public import stacks_project.Chap85.Lemma_85_2_3_Zariski
public import stacks_project.Chap85.Lemma_85_2_3

/-!
# Degreewise comparison for the Zariski site morphism of a simplicial space

A morphism `f : Y ⟶ X` of simplicial spaces induces `zariskiMap f : X_Zar ⥤ Y_Zar`.
Restriction of sheaves along `DiagramOpens.fiber` commutes with pushforward along this
site morphism, and the mixed Beck–Chevalley mate compares pullback along `zariskiMap f`
with ordinary inverse image along `f.app n`.
-/

@[expose]
public section

universe u

open CategoryTheory Functor TopologicalSpace TopCat

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject TopCat.{u}}

/-- The identity-on-objects isomorphism
`DiagramOpens.fiber X n ⋙ zariskiMap f ≅ Opens.map (f.app n) ⋙ DiagramOpens.fiber Y n`. -/
def zariskiMap_fiber (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ) :
    DiagramOpens.fiber X n ⋙ zariskiMap f ≅
      Opens.map (f.app n) ⋙ DiagramOpens.fiber Y n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- Components of `zariskiMap_fiber` are identity morphisms. -/
theorem zariskiMap_fiber_hom_app (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)
    (U : Opens (X.obj n)) :
    (zariskiMap_fiber f n).hom.app U = 𝟙 _ :=
  sorry

variable (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)
variable [(DiagramOpens.fiber X n).IsContinuous
    (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X)]
variable [(DiagramOpens.fiber Y n).IsContinuous
    (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y)]

/-- Continuity of the target composite of `zariskiMap_fiber`, transported from
`DiagramOpens.fiber X n ⋙ zariskiMap f`. -/
instance zariskiMap_fiber_isContinuous :
    (Opens.map (f.app n) ⋙ DiagramOpens.fiber Y n).IsContinuous
      (Opens.grothendieckTopology (X.obj n)) (zariskiTopology Y) :=
  isContinuous_comp' (zariskiMap_fiber f n)
    (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) (zariskiTopology Y)

/-- Pushforward along `zariskiMap f` then restrict to `X.obj n` is isomorphic to restrict
to `Y.obj n` then pushforward along `f.app n`. -/
def zariskiMap_pushforwardRestrict :
    (zariskiMap f).sheafPushforwardContinuous (Type u)
          (zariskiTopology X) (zariskiTopology Y) ⋙
        (DiagramOpens.fiber X n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) ≅
      (DiagramOpens.fiber Y n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y) ⋙
        TopCat.Sheaf.pushforward (Type u) (f.app n) :=
  sheafPushforwardContinuousComp' (zariskiMap_fiber f n) (Type u)
      (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) (zariskiTopology Y) ≪≫
    (sheafPushforwardContinuousComp (Opens.map (f.app n)) (DiagramOpens.fiber Y n) (Type u)
      (Opens.grothendieckTopology (X.obj n))
      (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y)).symm

variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology (Y.obj n)) (Type u)]
variable [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
variable [∀ P : (Opens (X.obj n))ᵒᵖ ⥤ Type u, (Opens.map (f.app n)).op.HasLeftKanExtension P]

/-- The mixed Beck–Chevalley mate
`(restrict_X ⋙ f_n⁻¹) ⟶ (f_Zar⁻¹ ⋙ restrict_Y)` of `zariskiMap_pushforwardRestrict`.
This is compared with `fiberPullbackIso.inv` by a separate proposition. -/
def zariskiMap_pullbackRestrict_mate :
    (DiagramOpens.fiber X n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X) ⋙
        TopCat.Sheaf.pullback (Type u) (f.app n) ⟶
      (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) ⋙
        (DiagramOpens.fiber Y n).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y) :=
  (mateEquiv
      ((zariskiMap f).sheafAdjunctionContinuous (Type u)
        (zariskiTopology X) (zariskiTopology Y))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f.app n))).symm
    (TwoSquare.mk _ _ _ _ (zariskiMap_pushforwardRestrict f n).hom)

/-- The mixed Beck–Chevalley isomorphism
`(f_Zar⁻¹ ⋙ restrict_Y) ≅ (restrict_X ⋙ f_n⁻¹)` obtained from uniqueness of
left adjoints to the explicit product right-extension square. -/
def zariskiMap_pullbackRestrict :
    (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) ⋙
      fiberRestriction Y n ≅
    fiberRestriction X n ⋙ TopCat.Sheaf.pullback (Type u) (f.app n) :=
  fiberPullbackIso f n

end CategoryTheory.SimplicialObject
