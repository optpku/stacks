/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.BivariantClass.Restriction

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 42.33.1: A degree-`p` bivariant class for `f : X ⟶ Y` assigns an
additive cap map on every locally finite-type cartesian base change, compatible
with proper pushforward, flat pullback of fixed relative dimension, and
effective-Cartier Gysin pullback. The collection denoted `A^p(X ⟶ Y)` is
represented by `AlgebraicGeometry.BivariantClass`.
-/
@[stacks 0B76] #check
  (AlgebraicGeometry.BivariantClass :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (p : ℤ), Type (u + 1))
