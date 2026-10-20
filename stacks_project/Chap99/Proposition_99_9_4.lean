module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Representability

/-!
# Proposition 99.9.4

If `f : X ⟶ B` is a finitely presented separated morphism of algebraic spaces
over a scheme `S`, then the Hilbert functor `Hilb_{X/B}` is an algebraic space
locally of finite presentation over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Proposition 99.9.4: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. If `f` is of finite presentation and separated, then
`Hilbert.hilbert f` (`Hilb_{X/B}`) is an algebraic space locally of finite presentation
over `B`. -/
@[stacks 0D01] #check
  (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert_isLocallyOfFinitePresentationOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] [Separated f],
      IsLocallyOfFinitePresentationOver (Hilbert.hilbert f))

/- If `f : X ⟶ B` is finitely presented and separated, then `Hilbert.hilbert f` is
represented by an algebraic space over `B`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hilbert.hilbert_isAlgebraicSpaceOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f], IsAlgebraicSpaceOver (Hilbert.hilbert f))
