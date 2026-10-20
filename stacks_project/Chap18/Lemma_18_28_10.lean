module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Exact
import StacksCheckRecall

/-!
# Lemma 18.28.10

Flat objects satisfy two-out-of-three on the left of a short exact sequence whose quotient is
flat.  The reusable owner is stated for any suitable monoidal abelian category.
-/

@[expose] public section

/- Lemma 18.28.10 (03EY), for presheaves of modules. -/
@[stacks 03EY "presheaf"]
#check @PresheafOfModules.flat_iff_flat_of_shortExact

/- Lemma 18.28.10 (03EY), for sheaves of modules. -/
@[stacks 03EY "sheaf"]
#check @SheafOfModules.RingedSite.flat_iff_flat_of_shortExact

/- The category-level two-out-of-three owner. -/
#check @CategoryTheory.MonoidalCategory.isFlat_left_iff_middle_of_shortExact
