/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Presheaf.Localization
import StacksCheckRecall

/-!
# Section 18.44: localization of ring presheaves

The reusable owner is the generic localization API for a compatible family of submonoids in a
commutative-ring-valued presheaf.  It applies on any category and specializes to the site used in
the chapter.
-/

@[expose] public section

/- Section 18.44 (0EMB): a compatible family of multiplicative subsets of local sections. -/
@[stacks 0EMB "compatible submonoid family"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf

/- Section 18.44 (0EMB): the explicit objectwise localization presheaf. -/
@[stacks 0EMB "localization presheaf"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.localizationPresheaf

/- Section 18.44 (0EMB): the canonical map into the localization presheaf. -/
@[stacks 0EMB "map to localization presheaf"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf

/- Section 18.44 (0EMB): the presheaf-level localization universal property. -/
@[stacks 0EMB "universal property"]
#check @CategoryTheory.Presheaf.SubmonoidPresheaf.Universal.existsUnique_lift
