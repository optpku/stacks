module

public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GeneralLinear.groupScheme :
  (R : Type u) → [CommRing R] → (I : Type u) → [Fintype I] → [DecidableEq I] →
    Grp (Over (Spec (CommRingCat.of R))))
