/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.CategoryTheory.Sites.Family.Cohomology
public import stacks_project.Chap85.Lemma_85_15_1_Site

/-!
# Component restriction along slice inclusion of a semi-representable site

The component restriction and its objectwise cohomology comparison are owned
by the shared family cohomology library.
-/

@[expose] public section

universe w v u z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/-- Each component slice inclusion is continuous for the family localization topology. -/
instance overIncl_isContinuous (K : FormalCoproduct.{w} C) (i : K.I) :
    (overIncl K i).IsContinuous (J.over (K.obj i)) (overTopology J K) :=
  CategoryTheory.Sigma.incl_isContinuous (fun index : K.I ↦ J.over (K.obj index)) i

#check (CategoryTheory.SemiRepresentableFamily.abelianComponentRestrict :
  ∀ {C : Type u} [Category.{v} C],
    (J : GrothendieckTopology C) →
    (K : FormalCoproduct.{w} C) → (i : K.I) →
    Sheaf (overTopology J K) AddCommGrpCat.{max w u v} ⥤
      Sheaf (J.over (K.obj i)) AddCommGrpCat.{max w u v})

#check (CategoryTheory.SemiRepresentableFamily.abelianComponentRestrict_obj_obj :
  ∀ {C : Type u} [Category.{v} C],
    (J : GrothendieckTopology C) →
    (K : FormalCoproduct.{w} C) → (i : K.I) →
    (G : Sheaf (overTopology J K) AddCommGrpCat.{max w u v}) →
    (U : overSlice K i) →
    ((abelianComponentRestrict J K i).obj G).obj.obj (Opposite.op U) =
      G.obj.obj (Opposite.op ((overIncl K i).obj U)))

#check (CategoryTheory.SemiRepresentableFamily.cohomologyOverObject_overIncl_iso :
  ∀ {C : Type u} [Category.{v} C],
    (J : GrothendieckTopology C) →
    (K : FormalCoproduct.{w} C) → (i : K.I) →
    (U : overSlice K i) →
    (G : Sheaf (overTopology J K) AddCommGrpCat.{max w u v}) →
    (p : ℕ) →
    [HasSheafify (overTopology J K) AddCommGrpCat.{max w u v}] →
    [HasExt.{z} (Sheaf (overTopology J K) AddCommGrpCat.{max w u v})] →
    [HasSheafify (J.over (K.obj i)) AddCommGrpCat.{max w u v}] →
    [HasExt.{z} (Sheaf (J.over (K.obj i)) AddCommGrpCat.{max w u v})] →
    IsIsomorphic
      (Sheaf.cohomologyOverObject.{z, 0} G ((overIncl K i).obj U) p)
      (Sheaf.cohomologyOverObject.{z, max w u}
        ((abelianComponentRestrict J K i).obj G) U p))

end CategoryTheory.SemiRepresentableFamily
