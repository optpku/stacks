/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.JRing.Criteria
import StacksCheckRecall

/-!
# Lemma 15.47.6

@stack 07PC
-/

@[expose] public section

/-! # Lemma 15.47.6: equivalent criteria for J-2 rings -/

/- Lemma 15.47.6 (1), tag `07PC`: the finite-type-domain criterion. -/
@[stacks 07PC "J-2 criterion by finite type domains"]
#check @IsJ2Ring.iff_finiteType_domain_isJ0

/- Lemma 15.47.6 (2), tag `07PC`: the finite-algebra criterion. -/
@[stacks 07PC "J-2 criterion by finite algebras"]
#check @IsJ2Ring.iff_finite_isJ1

/- Lemma 15.47.6 (3), tag `07PC`: the purely inseparable residue-field-model criterion. -/
@[stacks 07PC "J-2 criterion by residue-field models"]
#check @IsJ2Ring.iff_hasResidueModels

/- The source-facing four-way equivalence. -/
#check @IsJ2Ring.characterizations
