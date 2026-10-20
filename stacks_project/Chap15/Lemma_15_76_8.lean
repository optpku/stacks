module

public import ReasLib.Algebra.Homology.CochainComplex.Localization.Away.StableIso
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.76.8 (0F9V)

@stack 0F9V

The concrete localized complex, elementary contractible disk, finite-disk-sum property, and
stable-isomorphism theorem are owned by `CochainComplex.LocalizationAwayStable`.
-/

@[stacks 0F9V "Lemma 15.76.8 localized complex owner"]
#check @CategoryTheory.CochainComplex.LocalizationAwayStable.localized
@[stacks 0F9V "Lemma 15.76.8 elementary disk owner"]
#check @CategoryTheory.CochainComplex.LocalizationAwayStable.elementaryDisk
@[stacks 0F9V "Lemma 15.76.8 finite disk sums owner"]
#check @CategoryTheory.CochainComplex.LocalizationAwayStable.finiteDiskSums
@[stacks 0F9V "Lemma 15.76.8"]
#check @CategoryTheory.CochainComplex.LocalizationAwayStable.exists_stableIso
