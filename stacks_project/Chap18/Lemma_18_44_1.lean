/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Localization
import StacksCheckRecall

/-!
# Lemma 18.44.1

Sheaf localization is the sheafification of the explicit localization presheaf.  Its universal
property is exposed by the neutral ReasLib owner.
-/

@[expose] public section

/- Lemma 18.44.1 (0EMC): the sheaf obtained by sheafifying objectwise localization. -/
@[stacks 0EMC "localization sheaf"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.localizationSheaf

/- Lemma 18.44.1 (0EMC): the canonical morphism to the localization sheaf. -/
@[stacks 0EMC "canonical map"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.toLocalizationSheaf

/- Lemma 18.44.1 (0EMC): maps which invert the chosen sections factor uniquely through the
localization sheaf. -/
@[stacks 0EMC "universal property"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.LocalizationSheaf.existsUnique_lift
