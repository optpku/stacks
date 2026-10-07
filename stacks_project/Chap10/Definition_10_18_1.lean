module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.Group.Units.Hom
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.18.1

@stack 07BI
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.18.1: a local ring is the canonical mathlib predicate `IsLocalRing`. -/
@[stacks 07BI "local ring predicate"]
#check @IsLocalRing

/- Companion recall: for a local ring `R`, the unique maximal ideal is the canonical ideal
`IsLocalRing.maximalIdeal R`. -/
@[stacks 07BI "unique maximal ideal"]
#check @IsLocalRing.maximalIdeal

/- Companion recall: for a local ring `R`, the residue field is the quotient
`IsLocalRing.ResidueField R`. -/
@[stacks 07BI "residue field"]
#check @IsLocalRing.ResidueField

/- Companion recall: for a local ring `R`, the canonical residue map is
`IsLocalRing.residue R : R →+* IsLocalRing.ResidueField R`. -/
@[stacks 07BI "residue map"]
#check @IsLocalRing.residue

/- Companion recall: the canonical mathlib notion of a local ring homomorphism is `IsLocalHom`. -/
@[stacks 07BI "local ring homomorphism"]
#check @IsLocalHom
