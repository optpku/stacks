module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Acyclic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.5.1: for an affine morphism, every termwise quasi-coherent complex
computes its unbounded derived pushforward; equivalently, the canonical comparison
from termwise pushforward to derived pushforward is invertible. -/
@[stacks 0G9R] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforward.computesAt_of_isAffineHom :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
      (K : CochainComplex X.toRingedSpace.Modules ℤ)
      [Fact (CochainComplex.termsIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) K)],
      Functor.RightDerived.ComputesAt
        (Functor.Homotopy.toDerived (RingedSpace.Hom.pushforward f.toShHom))
        (HomotopyCategory.quasiIso X.toRingedSpace.Modules (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient X.toRingedSpace.Modules (ComplexShape.up ℤ)).obj K))
