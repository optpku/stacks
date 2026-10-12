/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Acyclic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.4.2: a complex of quasi-coherent modules that is termwise right-acyclic
for pushforward along a quasi-compact, quasi-separated morphism computes its unbounded
derived pushforward. -/
@[stacks 0G9N] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforward.computesAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      (K : CochainComplex X.toRingedSpace.Modules ℤ)
      (h_qc : CochainComplex.termsIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K)
      (h_acyclic : CochainComplex.termsIn
        (Functor.RightAcyclic.Bounded (RingedSpace.Hom.pushforward f.toShHom)) K),
      Functor.RightDerived.ComputesAt
        (Functor.Homotopy.toDerived (RingedSpace.Hom.pushforward f.toShHom))
        (HomotopyCategory.quasiIso X.toRingedSpace.Modules (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient X.toRingedSpace.Modules (ComplexShape.up ℤ)).obj K))
