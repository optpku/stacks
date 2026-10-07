module

public import stacks_project.Chap85.Lemma_85_2_4_Comparison
public import stacks_project.Chap85.Lemma_85_2_4_FiberRightAdjoint
public import stacks_project.Chap85.Lemma_85_2_4_RightSquare

/-!
# Lemma 85.2.4

Degreewise description of pushforward and pullback along the Zariski site morphism
of a morphism of simplicial spaces.
-/

@[expose]
public section

universe u

open CategoryTheory TopologicalSpace TopCat Opposite

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)
variable [(DiagramOpens.fiber X n).IsContinuous
    (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X)]
variable [(DiagramOpens.fiber Y n).IsContinuous
    (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y)]

/-- Lemma 85.2.4 (1): if `G` is a sheaf on `Y`, then `(f_Zar,* G)_n ≅ f_n,* G_n`, where
`F_n` is `fiberRestriction` along `DiagramOpens.fiber` as in Lemma 85.2.2, `f_Zar` is
`zariskiMap f` from Lemma 85.2.3, and `f_n,*` is ordinary pushforward along `f.app n`. -/
@[stacks 09VP]
def zariskiPushforward_component (G : Sheaf (zariskiTopology Y) (Type u)) :
    (fiberRestriction X n).obj
      (((zariskiMap f).sheafPushforwardContinuous (Type u)
        (zariskiTopology X) (zariskiTopology Y)).obj G) ≅
      (TopCat.Sheaf.pushforward (Type u) (f.app n)).obj ((fiberRestriction Y n).obj G) :=
  (zariskiMap_pushforwardRestrict f n).app G

/-- Sections of `(f_Zar,* G)_n` over an open of `X.obj n` agree with sections of `f_n,* G_n`. -/
theorem zariskiPushforward_component_obj (G : Sheaf (zariskiTopology Y) (Type u))
    (U : Opens (X.obj n)) :
    (((fiberRestriction X n).obj
        (((zariskiMap f).sheafPushforwardContinuous (Type u)
          (zariskiTopology X) (zariskiTopology Y)).obj G)).obj.obj (op U)) =
      (((TopCat.Sheaf.pushforward (Type u) (f.app n)).obj
        ((fiberRestriction Y n).obj G)).obj.obj (op U)) :=
  sorry

variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology (Y.obj n)) (Type u)]
variable [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
variable [∀ P : (Opens (X.obj n))ᵒᵖ ⥤ Type u, (Opens.map (f.app n)).op.HasLeftKanExtension P]

/-- Lemma 85.2.4 (2): if `F` is a sheaf on `X`, then `(f_Zar⁻¹ F)_n ≅ f_n⁻¹ F_n`, where
`F_n` is `fiberRestriction` along `DiagramOpens.fiber`, `f_Zar⁻¹` is sheaf pullback along
`zariskiMap f`, and `f_n⁻¹` is ordinary inverse image along `f.app n` (the sheafification of
the presheaf pullback of Sheaves, Lemma 6.21.3). The comparison is uniqueness of left
adjoints to the explicit product right-extension square. -/
@[stacks 09VP]
def zariskiPullback_component (F : Sheaf (zariskiTopology X) (Type u)) :
    (fiberRestriction Y n).obj
      (((zariskiMap f).sheafPullback (Type u)
        (zariskiTopology X) (zariskiTopology Y)).obj F) ≅
      (TopCat.Sheaf.pullback (Type u) (f.app n)).obj ((fiberRestriction X n).obj F) :=
  (fiberPullbackIso f n).app F

/-- The inverse of `fiberPullbackIso` agrees with the mixed mate of
`zariskiMap_pushforwardRestrict`. -/
theorem zariskiMap_pullbackRestrict_inv_eq_mate :
    (fiberPullbackIso f n).inv = zariskiMap_pullbackRestrict_mate f n :=
  sorry

end CategoryTheory.SimplicialObject
