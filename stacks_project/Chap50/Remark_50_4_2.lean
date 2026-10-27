/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DifferentialGradedAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.CupProduct
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open AlgebraicGeometry.Scheme.DeRham
open AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
open RingedSite.Hom

-- Use the same coefficient-module derived category as the recalled cup-product owner.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

/- Remark 50.4.2: a commutative square of schemes induces a canonical associative relative cup
product on the derived direct image of Ω^•_{X/S} in D(Y, q⁻¹𝒪_T). -/
@[stacks 0FU6]
#check (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.cupProduct :
  {X Y S T : Scheme} → (f : X ⟶ Y) → (p : X ⟶ S) → (q : Y ⟶ T) → (h : S ⟶ T) →
    (sq : CommSq f p q h) →
    [(modulePushforward (RingedSpace.DeRham.baseChangeHom
        (coefficientSheafedSquare f p q h sq))).IsRightAdjoint] →
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived
        (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))
      (ModuleQis (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))] →
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived
        (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))
      (ModuleQis (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))] →
    [DerivedAdjunction.HasPair
      (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))] →
    [MonoidalCategory
      (ModuleDerived (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))] →
    [MonoidalCategory
      (ModuleDerived (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))] →
    [(modulePullbackDerived
      (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))).OplaxMonoidal] →
    [(moduleLocalization
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).LaxMonoidal] →
    (modulePushforwardDerived
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p) ⊗
      (modulePushforwardDerived
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p) ⟶
      (modulePushforwardDerived
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p))

#check AlgebraicGeometry.Scheme.DeRham.deRhamDGA

#check AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.cupProduct_assoc

#check AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushedCohomologyCupProduct_compatibility
