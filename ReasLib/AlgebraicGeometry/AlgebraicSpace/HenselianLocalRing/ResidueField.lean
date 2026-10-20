module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Henselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField

/-!
# Residue fields of henselian local rings of algebraic spaces

The residue field of the henselian local ring of a decent algebraic space at a point
identifies with the residue field of the algebraic space at that point.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X}

/-- The residue field of a decent algebraic space at a point is isomorphic, after
universe lift, to the residue field of its henselian local ring. -/
theorem henselianLocalRing.residueField_nonempty_iso :
    Nonempty
      ((CommRingCat.universeLift.{u, u + 1}).obj (X.residueField x) ≅
        CommRingCat.of (IsLocalRing.ResidueField (henselianLocalRing X x))) :=
  sorry

/-- The residue field of a decent algebraic space at a point is ring-equivalent,
after `ULift`, to the residue field of its henselian local ring. -/
theorem henselianLocalRing.residueField_nonempty_ringEquiv :
    Nonempty
      (ULift.{u + 1} (X.residueField x : Type u) ≃+*
        IsLocalRing.ResidueField (henselianLocalRing X x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
