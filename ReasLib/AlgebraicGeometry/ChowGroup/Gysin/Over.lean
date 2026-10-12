/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The zero-scheme inclusion is proper when regarded as a morphism to an arbitrary
over-object with the same structure morphism. -/
instance (priority := low) zeroSchemeOverHomToObjectIsProper
    {S : Scheme.{u}} (X : Over S) (ℒ : X.left.Modules) [Invertible ℒ]
    (s : ℒ.sections) :
    IsProper ((Over.homMk (Scheme.zeroSchemeι ℒ s) :
      Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X).left) :=
  zeroSchemeOverHomIsProper X.hom ℒ s

end AlgebraicGeometry.Scheme.Modules
