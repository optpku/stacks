/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian

/-!
# Homology criterion for cartesian derived abelian sheaves on a fiberwise site
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- A derived abelian sheaf on a fiberwise simplicial site is cartesian if and only if
its homology sheaves in every integer degree are cartesian. -/
theorem AbelianDerived.isCartesian_iff_homology
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :
    AbelianDerived.IsCartesian F J K ↔
      ∀ q : ℤ, Sheaf.IsCartesian F J AddCommGrpCat.{w}
        ((DerivedCategory.homologyFunctor
          (Sheaf (topology F J) AddCommGrpCat.{w}) q).obj K) := sorry

end CategoryTheory.Grothendieck
