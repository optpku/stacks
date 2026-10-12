/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Neighborhood.LocalConsequences
import StacksCheckRecall

/-!
# Lemma 10.143.5
@stack 00U4
-/

@[expose] public section

/-!
# Lemma 10.143.5

The source's two local consequences of an etale basic-open neighborhood are
owned by the neutral `Algebra.Etale` bridge API in ReasLib.  This chapter file
retains only the labelled recalls.
-/

/- Lemma 10.143.5 (Tag 00U4): an etale basic-open neighborhood identifies the
extension of the contracted prime with the maximal ideal of the stalk. -/
@[stacks 00U4]
#check @Algebra.Etale.map_eq_maximalIdeal_of_exists_away

/- The source also identifies the extended prime `q S_q` with the maximal
ideal; Mathlib already owns this canonical localization equality. -/
@[stacks 00U4 "prime ideal at its local ring"]
#check @Localization.AtPrime.map_eq_maximalIdeal

/- Lemma 10.143.5 (Tag 00U4), finite residue-field clause. -/
@[stacks 00U4 "finite residue-field clause"]
#check @Algebra.Etale.residueField_finite_of_exists_away

/- Lemma 10.143.5 (Tag 00U4), separable residue-field clause. -/
@[stacks 00U4 "separable residue-field clause"]
#check @Algebra.Etale.residueField_isSeparable_of_exists_away
