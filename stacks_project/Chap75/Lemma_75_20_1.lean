module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.ProjectionFormula
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 75.20.1: for a quasi-compact and quasi-separated morphism of algebraic spaces
over a scheme `S`, the canonical map `Rf_* E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^* K)` is an
isomorphism when `E` and `K` have quasi-coherent cohomology. -/
@[stacks 08IN] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isIso_projectionFormula :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      (E : DerivedQCoh X) (K : DerivedQCoh Y),
      IsIso (leftMate f E.obj K.obj))
