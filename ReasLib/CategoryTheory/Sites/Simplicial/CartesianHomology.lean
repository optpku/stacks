/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian

/-!
# Homology criterion for cartesian derived abelian sheaves
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

variable [IsMorphismDiagram.{u, v, w} C J]

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (f : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map f).toFunctor).op.HasLeftKanExtension P]

section AbelianDerived

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- An object `K` of `D(C_total)` is cartesian if and only if
every homology sheaf `(DerivedCategory.homologyFunctor _ q).obj K` is a
cartesian abelian sheaf. -/
theorem AbelianDerived.isCartesian_iff_homology
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    AbelianDerived.IsCartesian C J K ↔
      ∀ q : ℤ, Abelian.IsCartesian C J
        ((DerivedCategory.homologyFunctor
          (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K) :=
  sorry

/-- The degree-`q` homology sheaf of a cartesian object of `D(C_total)` is cartesian. -/
instance AbelianDerived.instHomology_isCartesian
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [AbelianDerived.IsCartesian C J K] (q : ℤ) :
    Abelian.IsCartesian C J
      ((DerivedCategory.homologyFunctor
        (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K) :=
  sorry

/-- An object of `D(C_total)` whose homology sheaves are all cartesian is cartesian. -/
instance AbelianDerived.instIsCartesian_of_homology
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [∀ q : ℤ, Abelian.IsCartesian C J
      ((DerivedCategory.homologyFunctor
        (Sheaf (topology C J) AddCommGrpCat.{w}) q).obj K)] :
    AbelianDerived.IsCartesian C J K :=
  sorry

end AbelianDerived

end Abelian

end CategoryTheory.SimplicialSites
