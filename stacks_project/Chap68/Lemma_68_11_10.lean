module

public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing

/-!
# Residue field of the henselian local ring of a decent algebraic space

The residue field of the henselian local ring of a decent algebraic space at a point
identifies with the residue field of the algebraic space at that point.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X}

/-- Lemma 68.11.10: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. The residue field of the henselian local ring of `X` at `x` is
the residue field of `X` at `x`. The identification is a `CommRingCat` isomorphism
after `CommRingCat.universeLift`. -/
@[stacks 0EN0]
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
