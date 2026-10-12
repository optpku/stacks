/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GeneralLinear.groupScheme :
  (R : Type u) → [CommRing R] → (I : Type u) → [Fintype I] → [DecidableEq I] →
    Grp (Over (Spec (CommRingCat.of R))))
