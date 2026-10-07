module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import stacks_project.Chap85.Lemma_85_15_1_Site

/-!
# Component restriction along slice inclusion of a semi-representable site

The inclusion of the `i`-th slice `C / K.obj i` into `OverSite K` is continuous.
Abelian sheaves therefore restrict along `overIncl`, and objectwise cohomology
on `OverSite K` at `overIncl.obj U` agrees with cohomology of the restricted
sheaf on `C / K.obj i`.
-/

@[expose] public section

universe w v u z

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/-- The slice inclusion `overIncl K i : C / K.obj i ⥤ OverSite K` is continuous for
`J.over (K.obj i)` and `overTopology J K`. -/
instance overIncl_isContinuous (K : FormalCoproduct.{w} C) (i : K.I) :
    (overIncl K i).IsContinuous (J.over (K.obj i)) (overTopology J K) :=
  sorry

/-- Restriction of an abelian sheaf on `OverSite K` to the `i`-th slice
`C / K.obj i`, as continuous sheaf pushforward along `overIncl`. -/
abbrev abelianComponentRestrict (K : FormalCoproduct.{w} C) (i : K.I) :
    Sheaf (overTopology J K) AddCommGrpCat.{max w u v} ⥤
      Sheaf (J.over (K.obj i)) AddCommGrpCat.{max w u v} :=
  (overIncl K i).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
    (J.over (K.obj i)) (overTopology J K)

/-- `abelianComponentRestrict` is continuous sheaf pushforward along `overIncl`. -/
theorem abelianComponentRestrict_eq (K : FormalCoproduct.{w} C) (i : K.I) :
    abelianComponentRestrict J K i =
      (overIncl K i).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
        (J.over (K.obj i)) (overTopology J K) :=
  sorry

/-- Objectwise cohomology on `OverSite K` at `(overIncl K i).obj U` is isomorphic to
cohomology of the `i`-th component sheaf on `C / K.obj i`. -/
theorem cohomologyOverObject_overIncl_iso (K : FormalCoproduct.{w} C) (i : K.I)
    (U : overSlice K i) (G : Sheaf (overTopology J K) AddCommGrpCat.{max w u v})
    (p : ℕ)
    [HasSheafify (overTopology J K) AddCommGrpCat.{max w u v}]
    [HasExt.{z} (Sheaf (overTopology J K) AddCommGrpCat.{max w u v})]
    [HasSheafify (J.over (K.obj i)) AddCommGrpCat.{max w u v}]
    [HasExt.{z} (Sheaf (J.over (K.obj i)) AddCommGrpCat.{max w u v})] :
    IsIsomorphic
      (Sheaf.cohomologyOverObject.{z, 0} G ((overIncl K i).obj U) p)
      (Sheaf.cohomologyOverObject.{z, max w u}
        ((abelianComponentRestrict J K i).obj G) U p) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
