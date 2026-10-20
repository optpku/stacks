module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.ResidueField
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

/- Lemma 68.11.10: The residue field of the henselian local ring of a decent
algebraic space at a point is the residue field of the algebraic space at that point. -/
@[stacks 0EN0] #check
  (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.residueField_nonempty_iso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
    Nonempty
      ((CommRingCat.universeLift.{u, u + 1}).obj (X.residueField x) ≅
        CommRingCat.of (IsLocalRing.ResidueField (henselianLocalRing X x))))

#check
  (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.residueField_nonempty_ringEquiv :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
    Nonempty
      (ULift.{u + 1} (X.residueField x : Type u) ≃+*
        IsLocalRing.ResidueField (henselianLocalRing X x)))
