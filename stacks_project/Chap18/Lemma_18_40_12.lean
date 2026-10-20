module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.12 (04IH): localization to the slice over an object preserves locally ringedness. -/
@[stacks 04IH]
#check @Sheaf.IsLocallyRinged.over
