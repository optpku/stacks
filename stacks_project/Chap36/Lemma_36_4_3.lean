module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections.Acyclic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.4.3: on a quasi-compact and quasi-separated scheme, applying global
sections to a complex of quasi-coherent modules whose terms are right-acyclic for
global sections computes its unbounded derived global sections. -/
@[stacks 0G9P] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.globalSections.computesAt :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (K : CochainComplex X.toRingedSpace.Modules ℤ)
      (h_qc : CochainComplex.termsIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K)
      (h_acyclic : CochainComplex.termsIn
        (Functor.RightAcyclic.Bounded
          (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace)) K),
      Functor.RightDerived.ComputesAt
        (Functor.Homotopy.toDerived
          (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace))
        (HomotopyCategory.quasiIso X.toRingedSpace.Modules (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient X.toRingedSpace.Modules (ComplexShape.up ℤ)).obj K))
