/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Hom
open CategoryTheory.MonoidalCategory SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

variable {S X Y : Scheme.{u}}
variable (a : X ⟶ S) (b : Y ⟶ S)
variable (T : FiniteOrderDifferentialOperatorCat a ⥤
  FiniteOrderDifferentialOperatorCat b ⥤
    FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
variable (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
variable [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
variable [HomologicalComplex.HasMapBifunctor (operatorComplex a) (operatorComplex b) T (up ℕ)]
variable [HomologicalComplex.HasMapBifunctor
  (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)]

/- This bridge exposes the reusable total-complex comparison API. -/
#check (comparison :
  ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (T : FiniteOrderDifferentialOperatorCat a ⥤
      FiniteOrderDifferentialOperatorCat b ⥤
        FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    [HomologicalComplex.HasMapBifunctor (operatorComplex a) (operatorComplex b) T (up ℕ)]
    [HomologicalComplex.HasMapBifunctor
      (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)],
    externalDeRhamTotal a b T hT ⟶
      (RingedSpace.DeRham.complex
        (pullback.fst a b ≫ a).toLRSHom.toShHom).extend embeddingUpNat)

#check (comparison_isIso : ∀ {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (T : FiniteOrderDifferentialOperatorCat a ⥤
      FiniteOrderDifferentialOperatorCat b ⥤
        FiniteOrderDifferentialOperatorCat (pullback.fst a b ≫ a))
    (hT : IsExternalTensorProductFunctor a b (Functor.uncurry.obj T))
    [T.PreservesZeroMorphisms] [∀ M, (T.obj M).PreservesZeroMorphisms]
    [HomologicalComplex.HasMapBifunctor (operatorComplex a) (operatorComplex b) T (up ℕ)]
    [HomologicalComplex.HasMapBifunctor
      (extendedOperatorComplex a) (extendedOperatorComplex b) T (up ℤ)],
    IsIso (comparison a b T hT))

end AlgebraicGeometry.Scheme.DeRham.Kunneth
