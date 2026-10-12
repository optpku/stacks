/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Acyclic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.globalSections

/-- On a quasi-compact, quasi-separated scheme, a complex of quasi-coherent modules
that is termwise right-acyclic for global sections computes its unbounded derived
global sections. -/
theorem computesAt {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : CochainComplex X.toRingedSpace.Modules ℤ)
    (h_qc : CochainComplex.termsIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K)
    (h_acyclic : CochainComplex.termsIn
      (Functor.RightAcyclic.Bounded
        (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace)) K) :
    Functor.RightDerived.ComputesAt
      (Functor.Homotopy.toDerived
        (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace))
      (HomotopyCategory.quasiIso X.toRingedSpace.Modules (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient X.toRingedSpace.Modules (ComplexShape.up ℤ)).obj K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.globalSections
