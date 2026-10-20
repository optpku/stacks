module

import StacksCheckRecall
public import ReasLib.Topology.Sheaves.Simplicial.Functoriality

open CategoryTheory TopologicalSpace TopCat Opposite
universe u
namespace CategoryTheory.SimplicialObject
variable {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)
/- Lemma 85.2.4 (1): direct image is computed degreewise. -/
@[stacks 09VP] #check (CategoryTheory.SimplicialObject.zariskiPushforward_component f n :
    (G : Sheaf (zariskiTopology Y) (Type u)) →
    (sheafFiber X n (Type u)).obj
      (((zariskiMap f).sheafPushforwardContinuous (Type u)
        (zariskiTopology X) (zariskiTopology Y)).obj G) ≅
      (TopCat.Sheaf.pushforward (Type u) (f.app n)).obj ((sheafFiber Y n (Type u)).obj G))

variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology (Y.obj n)) (Type u)]
variable [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
variable [∀ P : (Opens (X.obj n))ᵒᵖ ⥤ Type u, (Opens.map (f.app n)).op.HasLeftKanExtension P]

/- Lemma 85.2.4 (2): inverse image is canonically computed degreewise. -/
@[stacks 09VP] #check (CategoryTheory.SimplicialObject.zariskiPullback_component f n :
    (F : Sheaf (zariskiTopology X) (Type u)) →
    (sheafFiber Y n (Type u)).obj
      (((zariskiMap f).sheafPullback (Type u)
        (zariskiTopology X) (zariskiTopology Y)).obj F) ≅
      (TopCat.Sheaf.pullback (Type u) (f.app n)).obj ((sheafFiber X n (Type u)).obj F))

end CategoryTheory.SimplicialObject
