/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Functor

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check
  (AlgebraicGeometry.Hilbert.functor :
    ∀ {S : Scheme.{u}} (X : Over S) (d : ℕ), (Over S)ᵒᵖ ⥤ Type u)
