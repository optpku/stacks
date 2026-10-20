module

public import ReasLib.RingTheory.GlobalDimension.RegularLocal
import StacksCheckRecall

/-!
# Regular Local Rings and Finite Global Dimension

@stack 00OC
-/

@[expose] public section

/- Proposition 10.110.5 (Stacks tag `00OC`): for a Noetherian local ring, the
residue field has finite projective dimension if and only if the ring has
finite global dimension, if and only if the ring is regular local. -/
@[stacks 00OC]
#check @IsRegularLocalRing.residueField_projectiveDimension_tfae

/- Proposition 10.110.5 (Stacks tag `00OC`, moreover): under these equivalent
conditions, the global dimension, Krull dimension, and cotangent-space
dimension agree. -/
#check @IsFiniteGlobalDimensionRing.globalDimension_eq_ringKrullDim
#check @IsFiniteGlobalDimensionRing.ringKrullDim_eq_finrank_cotangentSpace

/- Supporting owner-level implications used by the canonical result. -/
#check @IsLocalRing.ringKrullDim_le_finrank_cotangentSpace
#check @IsFiniteGlobalDimensionRing.residueField_projectiveDimension_ne_top
#check @IsRegularLocalRing.of_residueField_projectiveDimension_ne_top
#check @IsFiniteGlobalDimensionRing.finrank_cotangentSpace_le_globalDimension
