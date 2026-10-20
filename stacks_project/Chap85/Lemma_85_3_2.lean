/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Fiberwise
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {F : SimplicialObject Cat.{v, u}} (J : ∀ n, Precoverage (F.obj n))
variable [Grothendieck.IsFiberwiseSite F J]

/- Lemma 85.3.2: let `C` be a simplicial object of sites whose structure maps
`u_φ : C_n ⥤ C_m` are cocontinuous and have property `P`. Then the total site
`C_total` is the Grothendieck construction of `F : SimplicialObject Cat`, with
morphisms `(φ, f)` given by `Grothendieck.Hom` (base `φ : [m] ⟶ [n]` and fiber
`f : u_φ(U) ⟶ V`) and with selected coverings the identity-degree fiber families
`Grothendieck.ofFiber`. -/
@[stacks 09WD] #check (CategoryTheory.Grothendieck.precoverage.isSite F J :
  (CategoryTheory.Grothendieck.precoverage F J).IsSite)

#check (CategoryTheory.Grothendieck.precoverage F J :
  CategoryTheory.Precoverage (CategoryTheory.Grothendieck F))
