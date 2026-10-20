module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Locus

/-!
# Fitting loci of modules on algebraic spaces

Typed checks of the closed, open, and locally closed Fitting loci.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.fittingClosedSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ), ClosedSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.fittingOpenComplement :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ), OpenSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.fittingRankLocus :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ), LocallyClosedSubspace X)

