/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedSections
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition

/-!
# Lower-truncation completeness on the small pro-étale site

Every derived abelian sheaf is a homotopy limit of its lower-truncation tower,
and derived global sections preserve this homotopy-limit description.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open DerivedCategory.Truncation.Lower
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every derived abelian sheaf on the small pro-étale site is a homotopy limit
of its lower-truncation tower `n ↦ τ≥(-n) K`. -/
theorem isHomotopyLimit_lowerTruncationTower
    (X : Scheme.{u}) [HasSheafify (topology X) AddCommGrpCat.{u}]
    (K : DerivedCategory (Sheaf (topology X) AddCommGrpCat.{u})) :
    HomotopyLimit.IsOf (tower K) K := sorry

/-- Derived global sections of an abelian sheaf complex on the small pro-étale
site are a homotopy limit of the derived global sections of its lower truncations. -/
theorem globalSectionsDerived_isHomotopyLimit_lowerTruncationTower
    (X : Scheme.{u})
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (topology X) (globalProEt X)))
      (HomologicalComplex.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}) (up ℤ))]
    (K : DerivedCategory (Sheaf (topology X) AddCommGrpCat.{u})) :
    HomotopyLimit.IsOf (tower K ⋙ globalSectionsDerived X)
      ((globalSectionsDerived X).obj K) := sorry

end AlgebraicGeometry.Scheme.ProEt
