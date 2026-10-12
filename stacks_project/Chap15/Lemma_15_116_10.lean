/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.Section
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.10

Residue-map sections and their compatibility under local homomorphisms are owned by
`IsLocalRing.ResidueField.Section`.  This chapter file retains the two source clauses as tagged
checks and introduces no competing residue-field algebra instance.

@stack 09EZ
-/

@[stacks 09EZ "Lemma 15.116.10 (1)"]
#check @IsLocalRing.ResidueField.Section.exists_of_isNilpotent_maximalIdeal

@[stacks 09EZ "Lemma 15.116.10 (2)"]
#check @IsLocalRing.ResidueField.Section.exists_compatible

#check @IsLocalRing.ResidueField.Section
#check @IsLocalRing.ResidueField.Section.spec
#check @IsLocalRing.ResidueField.Section.nonempty_iff_exists_hom
#check @IsLocalRing.ResidueField.Section.Compatible
#check @IsLocalRing.ResidueField.Section.compatible_iff
#check @IsLocalRing.ResidueField.Section.exists_compatible_of_isNilpotent_maximalIdeal
