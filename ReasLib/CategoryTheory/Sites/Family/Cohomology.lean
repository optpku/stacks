/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Localization
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise

/-!
# Cohomology on component slices

Abelian sheaves on a family localization restrict to each component slice, and
their objectwise cohomology is preserved by this restriction.
-/

@[expose] public section

universe w v u z

open CategoryTheory CategoryTheory.Limits
open Opposite

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/-- Restriction of an abelian sheaf on a family localization to one component slice. -/
abbrev abelianComponentRestrict (K : FormalCoproduct.{w} C) (i : K.I) :
    Sheaf (overTopology J K) AddCommGrpCat.{max w u v} ⥤
      Sheaf (J.over (K.obj i)) AddCommGrpCat.{max w u v} :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (overIncl K i)
    AddCommGrpCat.{max w u v} _ (J.over (K.obj i)) (overTopology J K)
    (CategoryTheory.Sigma.incl_isContinuous
      (fun index : K.I ↦ J.over (K.obj index)) i)

/-- Evaluation of component restriction is precomposition along the slice inclusion. -/
@[simp]
theorem abelianComponentRestrict_obj_obj (K : FormalCoproduct.{w} C) (i : K.I)
    (G : Sheaf (overTopology J K) AddCommGrpCat.{max w u v}) (U : overSlice K i) :
    ((abelianComponentRestrict J K i).obj G).obj.obj (op U) =
      G.obj.obj (op ((overIncl K i).obj U)) := rfl

/-- Objectwise cohomology on a family localization at a component object is isomorphic to
cohomology of the restricted sheaf on that component slice. -/
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
