/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/- Remark 50.4.2: a commutative square of schemes induces a canonical associative relative cup
product on the derived direct image of Ω^•_{X/S} in D(Y, q⁻¹𝒪_T). -/
@[stacks 0FU6]
#check (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.cupProduct :
  {X Y S T : Scheme} → (f : X ⟶ Y) → (p : X ⟶ S) → (q : Y ⟶ T) → (h : S ⟶ T) →
    (sq : CommSq f p q h) →
    [((RingedSpace.DeRham.baseChangeHom
        (coefficientSheafedSquare f p q h sq)).modulePushforward).IsRightAdjoint] →
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
    [MonoidalCategory
      (HomotopyCategory
        (RingedSite.ModuleCat
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) (up ℤ))] →
    [(DerivedCategory.Qh :
      HomotopyCategory
        (RingedSite.ModuleCat
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) (up ℤ) ⥤
        ModuleDerived (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Monoidal] →
    [(HomotopyCategory.quotient
        (RingedSite.ModuleCat
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) (up ℤ)).LaxMonoidal] →
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
