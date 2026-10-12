/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap85.Lemma_85_2_4_FiberRightAdjoint
public import stacks_project.Chap85.Lemma_85_2_3
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The degreewise right-extension square -/
@[expose] public section
open CategoryTheory TopologicalSpace TopCat Opposite
noncomputable section
universe u
namespace CategoryTheory.SimplicialObject
variable {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)

/-- Naturality identifies the two actual inverse-image opens in the square. -/
theorem fiberRightSquare_open (U : DiagramOpens X) (a : n ⟶ U.base) :
    fiberOpen Y n ((zariskiMap f).obj U) a =
      (Opens.map (f.app n)).obj (fiberOpen X n U a) := by
  change (Opens.map (Y.map a)).obj ((Opens.map (f.app U.base)).obj U.opens) =
    (Opens.map (f.app n)).obj ((Opens.map (X.map a)).obj U.opens)
  rw [← Opens.map_comp_obj, ← Opens.map_comp_obj, f.naturality]

/-- Right extensions commute with pushforward by transporting each indexed section
along the equality of inverse-image opens proved from naturality of `f`. -/
def fiberRightSquare :
    fiberRight Y n ⋙ (zariskiMap f).sheafPushforwardContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y) ≅
    TopCat.Sheaf.pushforward (Type u) (f.app n) ⋙ fiberRight X n :=
  NatIso.ofComponents (fun G =>
    { hom := ⟨{ app := fun U => TypeCat.ofHom fun s a =>
                    G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a).symm).op (s a)
                naturality := sorry }⟩
      inv := ⟨{ app := fun U => TypeCat.ofHom fun s a =>
                    G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a)).op (s a)
                naturality := sorry }⟩
      hom_inv_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        ext s
        funext a
        change G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a)).op
          (G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a).symm).op (s a)) = s a
        rw [← types_comp_apply, ← G.obj.map_comp]
        simp
      inv_hom_id := by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        ext s
        funext a
        change G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a).symm).op
          (G.obj.map (eqToHom (fiberRightSquare_open f n U.unop a)).op (s a)) = s a
        rw [← types_comp_apply, ← G.obj.map_comp]
        simp }) (fun _ => sorry)

variable [(DiagramOpens.fiber X n).IsContinuous
    (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X)]
variable [(DiagramOpens.fiber Y n).IsContinuous
    (Opens.grothendieckTopology (Y.obj n)) (zariskiTopology Y)]
variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology (Y.obj n)) (Type u)]
variable [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
variable [∀ P : (Opens (X.obj n))ᵒᵖ ⥤ Type u, (Opens.map (f.app n)).op.HasLeftKanExtension P]

/-- The degreewise inverse-image comparison constructed from the explicit right
extensions and the actual sheaf pullback adjunctions. -/
def fiberPullbackIso :
    (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) ⋙
      fiberRestriction Y n ≅
    fiberRestriction X n ⋙ TopCat.Sheaf.pullback (Type u) (f.app n) :=
  Adjunction.leftAdjointUniq
    ((((zariskiMap f).sheafAdjunctionContinuous (Type u)
      (zariskiTopology X) (zariskiTopology Y)).comp
      (fiberRestrictionRightAdjunction Y n)).ofNatIsoRight (fiberRightSquare f n))
    ((fiberRestrictionRightAdjunction X n).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f.app n)))

end CategoryTheory.SimplicialObject
