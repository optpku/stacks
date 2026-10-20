module

public import ReasLib.AlgebraicGeometry.Hilbert.Functor

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check
  (AlgebraicGeometry.Hilbert.functor :
    ∀ {S : Scheme.{u}} (X : Over S) (d : ℕ), (Over S)ᵒᵖ ⥤ Type u)
