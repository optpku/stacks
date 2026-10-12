/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Over

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The zero-scheme inclusion is proper when regarded as a morphism to an arbitrary
over-object with the same structure morphism. -/
#check (AlgebraicGeometry.Scheme.Modules.zeroSchemeOverHomToObjectIsProper :
  ∀ {S : Scheme.{u}} (X : Over S) (ℒ : X.left.Modules)
    [Scheme.Modules.Invertible ℒ] (s : ℒ.sections),
    IsProper ((Over.homMk (Scheme.zeroSchemeι ℒ s) :
      Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X).left))
