/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian

/-!
# Morphisms from cartesian derived abelian sheaves on a fiberwise simplicial site
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u v w

namespace CategoryTheory.Grothendieck.AbelianDerived

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- A morphism from a cartesian derived abelian sheaf on a fiberwise simplicial
site is zero if its degree-zero restriction is zero, the degree-`n` Hom groups
shifted by `n` vanish for `n > 0`, and those shifted by `n + 1` vanish for every
`n ≥ 0`. -/
theorem hom_eq_zero
    (K K' : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    [IsCartesian F J K]
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((derivedRestrict F J n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (derivedRestrict F J n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((derivedRestrict F J n).obj K)⟦((n.len : ℤ) + 1)⟧ ⟶
        (derivedRestrict F J n).obj K'))
    (f : K ⟶ K') (hf0 : (derivedRestrict F J ⦋0⦌).map f = 0) :
    f = 0 := sorry

end CategoryTheory.Grothendieck.AbelianDerived
