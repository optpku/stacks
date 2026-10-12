/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Exact
import StacksCheckRecall

/-!
# Lemma 18.28.9

The two source statements are specializations of the reusable monoidal-abelian theorem: a short
exact sequence with flat quotient remains short exact after tensoring by an arbitrary object.
-/

@[expose] public section

/- Lemma 18.28.9 (1) (03EX): the presheaf-of-modules specialization. -/
@[stacks 03EX "(1)"]
#check @PresheafOfModules.shortExact_tensor_right_of_flat_quotient

/- Lemma 18.28.9 (2) (03EX): the sheaf-of-modules specialization. -/
@[stacks 03EX "(2)"]
#check @SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient

/- The category-level owner used by both specializations. -/
#check @CategoryTheory.MonoidalCategory.shortExact_map_tensorRight_of_flat_quotient
