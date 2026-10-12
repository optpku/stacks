/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.Acyclic.Right
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension
import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Affine
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.pushforward

/-- A complex of quasi-coherent modules that is termwise right-acyclic for pushforward along
a quasi-compact, quasi-separated morphism computes its unbounded derived pushforward. -/
theorem computesAt {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex X.toRingedSpace.Modules ℤ)
    (h_qc : CochainComplex.termsIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K)
    (h_acyclic : CochainComplex.termsIn
      (Functor.RightAcyclic.Bounded (RingedSpace.Hom.pushforward f.toShHom)) K) :
    Functor.RightDerived.ComputesAt
      (Functor.Homotopy.toDerived (RingedSpace.Hom.pushforward f.toShHom))
      (HomotopyCategory.quasiIso X.toRingedSpace.Modules (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient X.toRingedSpace.Modules (ComplexShape.up ℤ)).obj K) := sorry

/-- For an affine morphism of schemes, a termwise quasi-coherent complex computes its
unbounded derived pushforward. -/
theorem computesAt_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    (K : CochainComplex X.toRingedSpace.Modules ℤ)
    [Fact (CochainComplex.termsIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K)] :
    Functor.RightDerived.ComputesAt
      (Functor.Homotopy.toDerived (RingedSpace.Hom.pushforward f.toShHom))
      (HomotopyCategory.quasiIso X.toRingedSpace.Modules (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient X.toRingedSpace.Modules (ComplexShape.up ℤ)).obj K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.pushforward
