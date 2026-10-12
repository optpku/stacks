/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generator

universe u

#check (AlgebraicGeometry.ProjectiveSpace.beilinsonGenerator :
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules)
