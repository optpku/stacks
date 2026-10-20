module

public import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Cohomology

/-!
# Lemma 85.16.3

Objectwise cohomology of an abelian sheaf on `(C / K)_total` at an object of a
degree-`n` slice agrees with cohomology of the corresponding component of the
degree-`n` restriction.
-/

@[expose] public section

universe w v u z

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SemiRepresentableFamily

/- Lemma 85.16.3 -/
@[stacks 0DC0]
#check (CategoryTheory.SemiRepresentableFamily.cohomologyOverObject_component_iso :
  ∀ {C : Type u} [Category.{v} C],
    (J : GrothendieckTopology C) →
    (K : SimplicialObject (FormalCoproduct.{w} C)) →
    (n : SimplexCategory) →
    (i : (K.obj (op n)).I) →
    (U : overSlice (K.obj (op n)) i) →
    (F : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) →
    (p : ℕ) →
    [HasSheafify (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}] →
    [HasExt.{z} (Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v})] →
    [HasSheafify (J.over ((K.obj (op n)).obj i)) AddCommGrpCat.{max w u v}] →
    [HasExt.{z} (Sheaf (J.over ((K.obj (op n)).obj i)) AddCommGrpCat.{max w u v})] →
    IsIsomorphic
      (Sheaf.cohomologyOverObject.{z, 0} F
        ((Grothendieck.ι (overSiteDiagram K) (op n)).obj
          ((overIncl (K.obj (op n)) i).obj U)) p)
      (Sheaf.cohomologyOverObject.{z, max w u}
        ((abelianComponentRestrict J (K.obj (op n)) i).obj
          (((Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous
              AddCommGrpCat.{max w u v}
              (overTopology J (K.obj (op n))) (overSiteTotalTopology J K)).obj F))
        U p))

end CategoryTheory.SemiRepresentableFamily
