/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe uC uD vC vD wC wD

namespace CategoryTheory.Adjunction.Derived.ExactLeft

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
variable (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
variable [(Functor.Homotopy.toDerived R).HasRightDerivedFunctor
  (HomotopyCategory.quasiIso D (up ℤ))]

/-- The exact localization comparison postcomposed with a total right derived functor. -/
abbrev leftRightFactor :
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⋙
        (L.obj.mapDerivedCategory ⋙ Functor.RightDerived.Homotopy.functor R) ⟶
      (L.obj.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)) ⋙
          Functor.RightDerived.Homotopy.functor R :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.obj.mapDerivedCategoryFactors.hom
      (Functor.RightDerived.Homotopy.functor R)

/-- The cochain right-derived unit postcomposed with an exact derived functor. -/
abbrev rightLeftUnit :
    (R.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)) ⋙
          L.obj.mapDerivedCategory ⟶
      (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D) ⋙
        (Functor.RightDerived.Homotopy.functor R ⋙ L.obj.mapDerivedCategory) :=
  Functor.whiskerRight (Functor.RightDerived.Homotopy.cochainUnit R)
      L.obj.mapDerivedCategory ≫ (Functor.associator _ _ _).hom

/-- An exact localization comparison remains a left-derived comparison after
postcomposition with a total right derived functor. -/
instance leftRight_isLeftDerived :
    (L.obj.mapDerivedCategory ⋙ Functor.RightDerived.Homotopy.functor R).IsLeftDerivedFunctor
      (leftRightFactor L R) (HomologicalComplex.quasiIso C (up ℤ)) := sorry

/-- An exact left adjoint and a right-derived functor form a derived adjunction
when exact postcomposition preserves the specified right-derived universal property. -/
def adjunction (adj : L.obj ⊣ R)
    (h_rightLeft :
      (Functor.RightDerived.Homotopy.functor R ⋙ L.obj.mapDerivedCategory).IsRightDerivedFunctor
        (rightLeftUnit L R) (HomologicalComplex.quasiIso D (up ℤ))) :
    L.obj.mapDerivedCategory ⊣ Functor.RightDerived.Homotopy.functor R :=
  @CategoryTheory.Adjunction.derived
    _ _ _ _ _ _ _ _ _ _
    (CategoryTheory.Adjunction.mapHomologicalComplexAdjunction adj (up ℤ))
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)
    (HomologicalComplex.quasiIso C (up ℤ)) (HomologicalComplex.quasiIso D (up ℤ))
    inferInstance inferInstance L.obj.mapDerivedCategory
    (Functor.RightDerived.Homotopy.functor R) L.obj.mapDerivedCategoryFactors.hom
    (Functor.RightDerived.Homotopy.cochainUnit R)
    (Functor.LeftDerived.Exact.Cochain.isLeftDerived L.obj)
    (Functor.RightDerived.Homotopy.cochainIsRightDerived R)
    (leftRight_isLeftDerived L R) h_rightLeft

end CategoryTheory.Adjunction.Derived.ExactLeft
