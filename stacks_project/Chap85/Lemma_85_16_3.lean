module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import stacks_project.Chap85.Lemma_85_16_1_Localization
public import stacks_project.Chap85.Lemma_85_16_3_Component

/-!
# Lemma 85.16.3

Objectwise cohomology of an abelian sheaf on `(C / K)_total` at an object of a
degree-`n` slice agrees with cohomology of the corresponding component of the
degree-`n` restriction.
-/

@[expose] public section

universe w v u z

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))

/-- The fiber inclusion `ι` of `(C / K)_total` at degree `n` is continuous. -/
instance totalSite_ι_isContinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology J (K.obj (op n))) (overSiteTotalTopology J K) :=
  sorry

/-- Lemma 85.16.3: Let `C` be a site, `K` a simplicial object of `SR(C)`,
`U` an object of `C / U_{n,i}` in `C / K_n`, and `F` an abelian sheaf on
`(C / K)_total`. Then objectwise cohomology `H^p(U, F)` on `(C / K)_total`,
viewing `U` as `(ι (overSiteDiagram K) (op n)).obj ((overIncl (K.obj (op n)) i).obj U)`,
is isomorphic to `H^p(U, F_{n,i})` on `C / U_{n,i}`, where `F_n` is restriction of
`F` along `ι` and `F_{n,i}` is `abelianComponentRestrict` of `F_n`. -/
@[stacks 0DC0]
theorem cohomologyOverObject_component_iso
    (n : SimplexCategory) (i : (K.obj (op n)).I)
    (U : overSlice (K.obj (op n)) i)
    (F : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) (p : ℕ)
    [HasSheafify (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}]
    [HasExt.{z} (Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v})]
    [HasSheafify (J.over ((K.obj (op n)).obj i)) AddCommGrpCat.{max w u v}]
    [HasExt.{z} (Sheaf (J.over ((K.obj (op n)).obj i)) AddCommGrpCat.{max w u v})] :
    IsIsomorphic
      (Sheaf.cohomologyOverObject.{z, 0} F
        ((Grothendieck.ι (overSiteDiagram K) (op n)).obj
          ((overIncl (K.obj (op n)) i).obj U)) p)
      (Sheaf.cohomologyOverObject.{z, max w u}
        ((abelianComponentRestrict J (K.obj (op n)) i).obj
          (((Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous
              AddCommGrpCat.{max w u v}
              (overTopology J (K.obj (op n))) (overSiteTotalTopology J K)).obj F))
        U p) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
