/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian

/-!
# Closure of cartesian abelian sheaves on a fiberwise simplicial site
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

universe u v w u' v'

namespace CategoryTheory.Grothendieck.Sheaf

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- Cartesian abelian sheaves on the fiberwise total site of a simplicial diagram
of cocontinuous sites with property P form a weak Serre subcategory. -/
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass (cartesianProperty F J AddCommGrpCat.{w}) :=
  sorry

/-- A colimit of cartesian abelian sheaves on a fiberwise simplicial total site
is cartesian whenever that colimit exists. -/
instance cartesianProperty_isClosedUnderColimitsOfShape
    (ι : Type u') [Category.{v'} ι] :
    (cartesianProperty F J AddCommGrpCat.{w}).IsClosedUnderColimitsOfShape ι :=
  sorry

end CategoryTheory.Grothendieck.Sheaf
