/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Cech
import StacksCheckRecall

@[expose] public section

/- The Čech differential and augmentation are explicit reusable data built from the
localized-structure-module functor. -/
#check @SheafOfModules.Localization.Cech.differential
#check @SheafOfModules.Localization.Cech.augmentation
#check @SheafOfModules.Localization.Cech.shortComplex

/- Lemma 18.30.1 (1): the augmented Čech complex of a chosen covering family is exact at its
middle term. -/
@[stacks 0934 "(1)"]
#check @SheafOfModules.Localization.Cech.exactOfCoverage

/- Lemma 18.30.1 (2): the Čech augmentation of a chosen covering family is an epimorphism. -/
@[stacks 0934 "(2)"]
#check @SheafOfModules.Localization.Cech.augmentationEpiOfCoverage

/- The sieve-saturated versions are available when the site presentation is already a
Grothendieck topology. -/
#check @SheafOfModules.Localization.Cech.exact
#check @SheafOfModules.Localization.Cech.augmentation_epi
