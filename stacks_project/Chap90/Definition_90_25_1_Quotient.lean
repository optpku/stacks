/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap90.Definition_90_25_1_Groupoid
public import ReasLib.CategoryTheory.Groupoid.Quotient

/-!
# The quotient category cofibered in groupoids

The quotient `[U/R]` of a groupoid in functors is the category cofibered in groupoids
associated to the functor `C ⥤ Grpd` of fibre groupoids, realized by the Grothendieck
construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section
open scoped Bicategory BasedFunctor

universe u v w

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.GroupoidInFunctors

#check (CategoryTheory.GroupoidInFunctors.quotientFunctor :
  (G : GroupoidInFunctors.{u, v, w} C) →
    Grothendieck (G.toFunctor ⋙ Grpd.forgetToCat) ⥤ C)

#check (CategoryTheory.GroupoidInFunctors.quotientFunctor_op_inGroupoids :
  (G : GroupoidInFunctors.{u, v, w} C) →
    Functor.IsFibered.InGroupoids (quotientFunctor G).op)

#check (CategoryTheory.GroupoidInFunctors.quotient :
  GroupoidInFunctors.{u, v, w} C → CofiberedCategoryOver.Groupoids C)

#check (CategoryTheory.GroupoidInFunctors.quotient_p :
  (G : GroupoidInFunctors.{u, v, w} C) →
    (quotient G).p = quotientFunctor G)

#check (CategoryTheory.GroupoidInFunctors.quotient_total :
  (G : GroupoidInFunctors.{u, v, w} C) →
    (quotient G).total = Grothendieck (G.toFunctor ⋙ Grpd.forgetToCat))

end CategoryTheory.GroupoidInFunctors
