/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute

@[expose] public section

open AlgebraicGeometry CategoryTheory TopCat
open scoped AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (X : Scheme.{u}) [Scheme.IsCharP X p]

/- Definition 33.36.1: The absolute Frobenius of a scheme in characteristic `p`
has identity underlying topological map and acts on sections by `g ↦ g ^ p`. -/
@[stacks 03SM]
#check (AlgebraicGeometry.Scheme.absoluteFrobenius p X : X ⟶ X)

#check (AlgebraicGeometry.Scheme.absoluteFrobenius_base p X :
  (AlgebraicGeometry.Scheme.absoluteFrobenius p X).base = 𝟙 (X : TopCat))

#check (AlgebraicGeometry.Scheme.absoluteFrobenius_appLE p X :
  ∀ (U : X.Opens) (s : Γ(X, U)),
    CommRingCat.Hom.hom
        ((AlgebraicGeometry.Scheme.absoluteFrobenius p X).appLE U U le_rfl) s =
      s ^ p)
