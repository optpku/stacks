/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.LowerShriek.AssociatedSheaf
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

/-!
# Lemma 7.25.2

The associated-sheaf comparison for localization lower shriek is owned by
`ReasLib.CategoryTheory.Sites.Localization.LowerShriek.AssociatedSheaf`.
-/

/- Lemma 7.25.2 (03CD): localization lower shriek applied to the sheafification
of a presheaf on `C / U` is canonically the sheafification of its left Kan
extension along `(Over.forget U).op`. -/
@[stacks 03CD] #check @localization_lowerShriek_associatedSheafIso

#check @localization_lowerShriek_toSheafify_map_isIso
