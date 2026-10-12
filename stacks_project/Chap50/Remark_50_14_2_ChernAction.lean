/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle

open AlgebraicGeometry CategoryTheory
open RingedSite.Hom AlgebraicGeometry.Scheme.DeRham.DerivedPushforward

universe u

/- Compatibility checks for the supplied-realization tautological Chern action. -/
#check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.firstChernMap :
  ∀ {S X P : Scheme.{u}} {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (_ : Scheme.ProjectiveBundle.Representation π E)
    (_ : Scheme.DeRham.LogarithmicForms.ChernComparison (π ≫ f)),
    ShiftedHom (derivedComplex (π ≫ f)) (derivedComplex (π ≫ f)) (2 : ℤ))

#check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.chernMapDegree : ℕ → ℤ)

#check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.chernMapDegree_eq :
  ∀ degree : ℕ, Scheme.DeRham.ProjectiveBundle.chernMapDegree degree = 2 * (degree : ℤ))

#check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.chernMapPower :
  ∀ {S X P : Scheme.{u}} {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (_ : Scheme.ProjectiveBundle.Representation π E)
    (_ : Scheme.DeRham.LogarithmicForms.ChernComparison (π ≫ f)) (degree : ℕ),
    ShiftedHom (derivedComplex (π ≫ f)) (derivedComplex (π ≫ f))
      (Scheme.DeRham.ProjectiveBundle.chernMapDegree degree))

#check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.pushedFirstChernMap :
  ∀ {S X P : Scheme.{u}} {E : X.Modules} (f : X ⟶ S) (π : P ⟶ X)
    (_ : Scheme.ProjectiveBundle.Representation π E)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (Scheme.DeRham.Cohomology.coefficientHom
          (Scheme.DeRham.ProjectiveBundle.structureSquare f π)))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))]
    (_ : Scheme.DeRham.LogarithmicForms.ChernComparison (π ≫ f)),
    ShiftedHom
      ((modulePushforwardDerived.{u}
        (Scheme.DeRham.Cohomology.coefficientHom
          (Scheme.DeRham.ProjectiveBundle.structureSquare f π))).obj
        (derivedComplex (π ≫ f)))
      ((modulePushforwardDerived.{u}
        (Scheme.DeRham.Cohomology.coefficientHom
          (Scheme.DeRham.ProjectiveBundle.structureSquare f π))).obj
        (derivedComplex (π ≫ f))) (2 : ℤ))
