/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian

/-!
# Morphisms from cartesian derived abelian sheaves on a simplicial site
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u v w

namespace CategoryTheory.SimplicialSites.AbelianDerived

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
include instMorphismDiagram instWeakSheafify instLeftKan
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- A morphism from a cartesian derived abelian sheaf is zero if its degree-zero
restriction is zero, the degree-`n` Hom groups shifted by `n` vanish for `n > 0`,
and those shifted by `n + 1` vanish for every `n ≥ 0`. -/
theorem hom_eq_zero
    (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [IsCartesian C J K]
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((derivedRestrict C J n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (derivedRestrict C J n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((derivedRestrict C J n).obj K)⟦((n.len : ℤ) + 1)⟧ ⟶
        (derivedRestrict C J n).obj K'))
    (f : K ⟶ K') (hf0 : (derivedRestrict C J ⦋0⦌).map f = 0) :
    f = 0 := sorry

/-- Two morphisms from a cartesian derived abelian sheaf are equal if their
degree-zero restrictions agree, the degree-`n` Hom groups shifted by `n` vanish
for `n > 0`, and those shifted by `n + 1` vanish for every `n ≥ 0`. -/
theorem hom_eq_of_eq_component
    (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [IsCartesian C J K]
    (h_hom : ∀ n : SimplexCategory, 0 < n.len →
      Subsingleton (((derivedRestrict C J n).obj K)⟦(n.len : ℤ)⟧ ⟶
        (derivedRestrict C J n).obj K'))
    (h_hom_succ : ∀ n : SimplexCategory,
      Subsingleton (((derivedRestrict C J n).obj K)⟦((n.len : ℤ) + 1)⟧ ⟶
        (derivedRestrict C J n).obj K'))
    (f g : K ⟶ K')
    (hfg : (derivedRestrict C J ⦋0⦌).map f = (derivedRestrict C J ⦋0⦌).map g) :
    f = g := sorry

end CategoryTheory.SimplicialSites.AbelianDerived
