module

public import ReasLib.RingTheory.Henselian.ArtinianQuotient
import StacksCheckRecall

/-!
# Permanence data for henselizations

Lemma 15.45.1 records faithful flatness, maximal-ideal compatibility, Artinian quotient
comparisons, and compatible quotient bases for henselizations and strict henselizations.

@stack 07QM
-/

@[expose] public section

@[stacks 07QM "Lemma 15.45.1 (1)"]
#check @IsHenselizationOf.faithfullyFlat

@[stacks 07QM "Lemma 15.45.1 (2)"]
#check @IsStrictHenselizationOf.faithfullyFlat

@[stacks 07QM "Lemma 15.45.1 (3)"]
#check @IsHenselizationOf.map_maximalIdeal

@[stacks 07QM "Lemma 15.45.1 (4)"]
#check @IsStrictHenselizationOf.map_baseMaximalIdeal_eq_map_henselizationMaximalIdeal

@[stacks 07QM "Lemma 15.45.1 (5)"]
#check @IsStrictHenselizationOf.map_maximalIdeal

@[stacks 07QM "Lemma 15.45.1 (6)"]
#check @IsHenselizationOf.quotientPowMap_bijective

@[stacks 07QM "Lemma 15.45.1 (7)"]
#check @IsStrictHenselizationOf.exists_quotientPow_basis_lifts
